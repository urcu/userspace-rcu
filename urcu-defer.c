/*
 * urcu-defer.c
 *
 * Userspace RCU library - batch memory reclamation
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

#include <stdio.h>
#include <pthread.h>
#include <signal.h>
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <poll.h>
#include <sys/time.h>
#include <syscall.h>
#include <unistd.h>

#include "urcu/urcu-futex.h"
#include "urcu-defer-static.h"
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include "urcu-defer.h"

void __attribute__((destructor)) rcu_defer_exit(void);

extern void synchronize_rcu(void);

/*
 * rcu_defer_mutex nests inside defer_thread_mutex.
 */
static pthread_mutex_t rcu_defer_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t defer_thread_mutex = PTHREAD_MUTEX_INITIALIZER;

static int defer_thread_futex;

/*
 * Written to only by each individual deferer. Read by both the deferer and
 * the reclamation tread.
 */
static struct defer_queue __thread defer_queue;
static LIST_HEAD(registry);
static pthread_t tid_defer;

static void mutex_lock(pthread_mutex_t *mutex)
{
	int ret;

#ifndef DISTRUST_SIGNALS_EXTREME
	ret = pthread_mutex_lock(mutex);
	if (ret) {
		perror("Error in pthread mutex lock");
		exit(-1);
	}
#else /* #ifndef DISTRUST_SIGNALS_EXTREME */
	while ((ret = pthread_mutex_trylock(mutex)) != 0) {
		if (ret != EBUSY && ret != EINTR) {
			printf("ret = %d, errno = %d\n", ret, errno);
			perror("Error in pthread mutex lock");
			exit(-1);
		}
		pthread_testcancel();
		poll(NULL,0,10);
	}
#endif /* #else #ifndef DISTRUST_SIGNALS_EXTREME */
}

static void mutex_unlock(pthread_mutex_t *mutex)
{
	int ret;

	ret = pthread_mutex_unlock(mutex);
	if (ret) {
		perror("Error in pthread mutex unlock");
		exit(-1);
	}
}

/*
 * Wake-up any waiting defer thread. Called from many concurrent threads.
 */
static void wake_up_defer(void)
{
	if (unlikely(uatomic_read(&defer_thread_futex) == -1)) {
		uatomic_set(&defer_thread_futex, 0);
		futex_noasync(&defer_thread_futex, FUTEX_WAKE, 1,
		      NULL, NULL, 0);
	}
}

static unsigned long rcu_defer_num_callbacks(void)
{
	unsigned long num_items = 0, head;
	struct defer_queue *index;

	mutex_lock(&rcu_defer_mutex);
	list_for_each_entry(index, &registry, list) {
		head = LOAD_SHARED(index->head);
		num_items += head - index->tail;
	}
	mutex_unlock(&rcu_defer_mutex);
	return num_items;
}

/*
 * Defer thread waiting. Single thread.
 */
static void wait_defer(void)
{
	uatomic_dec(&defer_thread_futex);
	smp_mb();	/* Write futex before read queue */
	if (rcu_defer_num_callbacks()) {
		smp_mb();	/* Read queue before write futex */
		/* Callbacks are queued, don't wait. */
		uatomic_set(&defer_thread_futex, 0);
	} else {
		smp_rmb();	/* Read queue before read futex */
		if (uatomic_read(&defer_thread_futex) == -1)
			futex_noasync(&defer_thread_futex, FUTEX_WAIT, -1,
			      NULL, NULL, 0);
	}
}

/*
 * Must be called after Q.S. is reached.
 */
static void rcu_defer_barrier_queue(struct defer_queue *queue,
				    unsigned long head)
{
	unsigned long i;
	void (*fct)(void *p);
	void *p;

	/*
	 * Tail is only modified when lock is held.
	 * Head is only modified by owner thread.
	 */

	for (i = queue->tail; i != head;) {
		smp_rmb();       /* read head before q[]. */
		p = LOAD_SHARED(queue->q[i++ & DEFER_QUEUE_MASK]);
		if (unlikely(DQ_IS_FCT_BIT(p))) {
			DQ_CLEAR_FCT_BIT(p);
			queue->last_fct_out = p;
			p = LOAD_SHARED(queue->q[i++ & DEFER_QUEUE_MASK]);
		} else if (unlikely(p == DQ_FCT_MARK)) {
			p = LOAD_SHARED(queue->q[i++ & DEFER_QUEUE_MASK]);
			queue->last_fct_out = p;
			p = LOAD_SHARED(queue->q[i++ & DEFER_QUEUE_MASK]);
		}
		fct = queue->last_fct_out;
		fct(p);
	}
	smp_mb();	/* push tail after having used q[] */
	STORE_SHARED(queue->tail, i);
}

static void _rcu_defer_barrier_thread(void)
{
	unsigned long head, num_items;

	head = defer_queue.head;
	num_items = head - defer_queue.tail;
	if (unlikely(!num_items))
		return;
	synchronize_rcu();
	rcu_defer_barrier_queue(&defer_queue, head);
}

void rcu_defer_barrier_thread(void)
{
	mutex_lock(&rcu_defer_mutex);
	_rcu_defer_barrier_thread();
	mutex_unlock(&rcu_defer_mutex);
}

/*
 * rcu_defer_barrier - Execute all queued rcu callbacks.
 *
 * Execute all RCU callbacks queued before rcu_defer_barrier() execution.
 * All callbacks queued on the local thread prior to a rcu_defer_barrier() call
 * are guaranteed to be executed.
 * Callbacks queued by other threads concurrently with rcu_defer_barrier()
 * execution are not guaranteed to be executed in the current batch (could
 * be left for the next batch). These callbacks queued by other threads are only
 * guaranteed to be executed if there is explicit synchronization between
 * the thread adding to the queue and the thread issuing the defer_barrier call.
 */

void rcu_defer_barrier(void)
{
	struct defer_queue *index;
	unsigned long num_items = 0;

	if (list_empty(&registry))
		return;

	mutex_lock(&rcu_defer_mutex);
	list_for_each_entry(index, &registry, list) {
		index->last_head = LOAD_SHARED(index->head);
		num_items += index->last_head - index->tail;
	}
	if (likely(!num_items)) {
		/*
		 * We skip the grace period because there are no queued
		 * callbacks to execute.
		 */
		goto end;
	}
	synchronize_rcu();
	list_for_each_entry(index, &registry, list)
		rcu_defer_barrier_queue(index, index->last_head);
end:
	mutex_unlock(&rcu_defer_mutex);
}

/*
 * _defer_rcu - Queue a RCU callback.
 */
void _defer_rcu(void (*fct)(void *p), void *p)
{
	unsigned long head, tail;

	/*
	 * Head is only modified by ourself. Tail can be modified by reclamation
	 * thread.
	 */
	head = defer_queue.head;
	tail = LOAD_SHARED(defer_queue.tail);

	/*
	 * If queue is full, or reached threshold. Empty queue ourself.
	 * Worse-case: must allow 2 supplementary entries for fct pointer.
	 */
	if (unlikely(head - tail >= DEFER_QUEUE_SIZE - 2)) {
		assert(head - tail <= DEFER_QUEUE_SIZE);
		rcu_defer_barrier_thread();
		assert(head - LOAD_SHARED(defer_queue.tail) == 0);
	}

	if (unlikely(defer_queue.last_fct_in != fct)) {
		defer_queue.last_fct_in = fct;
		if (unlikely(DQ_IS_FCT_BIT(fct) || fct == DQ_FCT_MARK)) {
			/*
			 * If the function to encode is not aligned or the
			 * marker, write DQ_FCT_MARK followed by the function
			 * pointer.
			 */
			_STORE_SHARED(defer_queue.q[head++ & DEFER_QUEUE_MASK],
				      DQ_FCT_MARK);
			_STORE_SHARED(defer_queue.q[head++ & DEFER_QUEUE_MASK],
				      fct);
		} else {
			DQ_SET_FCT_BIT(fct);
			_STORE_SHARED(defer_queue.q[head++ & DEFER_QUEUE_MASK],
				      fct);
		}
	} else {
		if (unlikely(DQ_IS_FCT_BIT(p) || p == DQ_FCT_MARK)) {
			/*
			 * If the data to encode is not aligned or the marker,
			 * write DQ_FCT_MARK followed by the function pointer.
			 */
			_STORE_SHARED(defer_queue.q[head++ & DEFER_QUEUE_MASK],
				      DQ_FCT_MARK);
			_STORE_SHARED(defer_queue.q[head++ & DEFER_QUEUE_MASK],
				      fct);
		}
	}
	_STORE_SHARED(defer_queue.q[head++ & DEFER_QUEUE_MASK], p);
	smp_wmb();	/* Publish new pointer before head */
			/* Write q[] before head. */
	STORE_SHARED(defer_queue.head, head);
	smp_mb();	/* Write queue head before read futex */
	/*
	 * Wake-up any waiting defer thread.
	 */
	wake_up_defer();
}

void *thr_defer(void *args)
{
	for (;;) {
		pthread_testcancel();
		/*
		 * "Be green". Don't wake up the CPU if there is no RCU work
		 * to perform whatsoever. Aims at saving laptop battery life by
		 * leaving the processor in sleep state when idle.
		 */
		wait_defer();
		/* Sleeping after wait_defer to let many callbacks enqueue */
		poll(NULL,0,100);	/* wait for 100ms */
		rcu_defer_barrier();
	}

	return NULL;
}

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

void defer_rcu(void (*fct)(void *p), void *p)
{
	_defer_rcu(fct, p);
}

static void start_defer_thread(void)
{
	int ret;

	ret = pthread_create(&tid_defer, NULL, thr_defer, NULL);
	assert(!ret);
}

static void stop_defer_thread(void)
{
	int ret;
	void *tret;

	pthread_cancel(tid_defer);
	wake_up_defer();
	ret = pthread_join(tid_defer, &tret);
	assert(!ret);
}

void rcu_defer_register_thread(void)
{
	int was_empty;

	assert(defer_queue.last_head == 0);
	assert(defer_queue.q == NULL);
	defer_queue.q = malloc(sizeof(void *) * DEFER_QUEUE_SIZE);

	mutex_lock(&defer_thread_mutex);
	mutex_lock(&rcu_defer_mutex);
	was_empty = list_empty(&registry);
	list_add(&defer_queue.list, &registry);
	mutex_unlock(&rcu_defer_mutex);

	if (was_empty)
		start_defer_thread();
	mutex_unlock(&defer_thread_mutex);
}

void rcu_defer_unregister_thread(void)
{
	int is_empty;

	mutex_lock(&defer_thread_mutex);
	mutex_lock(&rcu_defer_mutex);
	list_del(&defer_queue.list);
	_rcu_defer_barrier_thread();
	free(defer_queue.q);
	defer_queue.q = NULL;
	is_empty = list_empty(&registry);
	mutex_unlock(&rcu_defer_mutex);

	if (is_empty)
		stop_defer_thread();
	mutex_unlock(&defer_thread_mutex);
}

void rcu_defer_exit(void)
{
	assert(list_empty(&registry));
}
