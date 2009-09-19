/*
 * urcu-reclaim.c
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

#include "urcu-reclaim-static.h"
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include "urcu-reclaim.h"

void __attribute__((destructor)) urcu_reclaim_exit(void);

extern void synchronize_rcu(void);

/*
 * urcu_reclaim_mutex nests inside reclaim_thread_mutex.
 */
static pthread_mutex_t urcu_reclaim_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t reclaim_thread_mutex = PTHREAD_MUTEX_INITIALIZER;

/*
 * Written to only by each individual reclaimer. Read by both the reclaimer and
 * the reclamation tread.
 */
struct reclaim_queue __thread reclaim_queue;

/* Thread IDs of registered reclaimers */
#define INIT_NUM_THREADS 4

struct reclaimer_registry {
	pthread_t tid;
	struct reclaim_queue *reclaim_queue;
	unsigned long last_head;
};

static struct reclaimer_registry *registry;
static int num_reclaimers, alloc_reclaimers;

static pthread_t tid_reclaim;
static int exit_reclaim;

static void internal_urcu_lock(pthread_mutex_t *mutex)
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
		poll(NULL,0,10);
	}
#endif /* #else #ifndef DISTRUST_SIGNALS_EXTREME */
}

static void internal_urcu_unlock(pthread_mutex_t *mutex)
{
	int ret;

	ret = pthread_mutex_unlock(mutex);
	if (ret) {
		perror("Error in pthread mutex unlock");
		exit(-1);
	}
}

/*
 * Must be called after Q.S. is reached.
 */
static void rcu_reclaim_barrier_queue(struct reclaim_queue *queue,
				      unsigned long head)
{
	unsigned long i;

	/*
	 * Tail is only modified when lock is held.
	 * Head is only modified by owner thread.
	 */

	for (i = queue->tail; i != head; i++) {
		smp_rmb();       /* read head before q[]. */
		free(LOAD_SHARED(queue->q[i & RECLAIM_QUEUE_MASK]));
	}
	smp_mb();	/* push tail after having used q[] */
	STORE_SHARED(queue->tail, i);
}

static void _rcu_reclaim_barrier_thread(void)
{
	unsigned long head;

	head = reclaim_queue.head;
	synchronize_rcu();
	rcu_reclaim_barrier_queue(&reclaim_queue, head);
}


void rcu_reclaim_barrier_thread(void)
{
	internal_urcu_lock(&urcu_reclaim_mutex);
	_rcu_reclaim_barrier_thread();
	internal_urcu_unlock(&urcu_reclaim_mutex);
}

void rcu_reclaim_barrier(void)
{
	struct reclaimer_registry *index;

	if (!registry)
		return;

	internal_urcu_lock(&urcu_reclaim_mutex);
	for (index = registry; index < registry + num_reclaimers; index++)
		index->last_head = LOAD_SHARED(index->reclaim_queue->head);
	synchronize_rcu();
	for (index = registry; index < registry + num_reclaimers; index++)
		rcu_reclaim_barrier_queue(index->reclaim_queue,
					  index->last_head);
	internal_urcu_unlock(&urcu_reclaim_mutex);
}

void *thr_reclaim(void *args)
{
	for (;;) {
		if (LOAD_SHARED(exit_reclaim))
			break;
		poll(NULL,0,100);	/* wait for 100ms */
		rcu_reclaim_barrier();
	}

	return NULL;
}

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

void rcu_reclaim_queue(void *p)
{
	_rcu_reclaim_queue(p);
}

static void rcu_add_reclaimer(pthread_t id)
{
	struct reclaimer_registry *oldarray;

	if (!registry) {
		alloc_reclaimers = INIT_NUM_THREADS;
		num_reclaimers = 0;
		registry =
			malloc(sizeof(struct reclaimer_registry) * alloc_reclaimers);
	}
	if (alloc_reclaimers < num_reclaimers + 1) {
		oldarray = registry;
		registry = malloc(sizeof(struct reclaimer_registry)
				* (alloc_reclaimers << 1));
		memcpy(registry, oldarray,
			sizeof(struct reclaimer_registry) * alloc_reclaimers);
		alloc_reclaimers <<= 1;
		free(oldarray);
	}
	registry[num_reclaimers].tid = id;
	/* reference to the TLS of _this_ reclaimer thread. */
	registry[num_reclaimers].reclaim_queue = &reclaim_queue;
	num_reclaimers++;
}

/*
 * Never shrink (implementation limitation).
 * This is O(nb threads). Eventually use a hash table.
 */
static void rcu_remove_reclaimer(pthread_t id)
{
	struct reclaimer_registry *index;

	assert(registry != NULL);
	for (index = registry; index < registry + num_reclaimers; index++) {
		if (pthread_equal(index->tid, id)) {
			memcpy(index, &registry[num_reclaimers - 1],
				sizeof(struct reclaimer_registry));
			registry[num_reclaimers - 1].tid = 0;
			registry[num_reclaimers - 1].reclaim_queue = NULL;
			num_reclaimers--;
			return;
		}
	}
	/* Hrm not found, forgot to register ? */
	assert(0);
}

static void start_reclaim_thread(void)
{
	int ret;

	ret = pthread_create(&tid_reclaim, NULL, thr_reclaim,
		NULL);
	assert(!ret);
}

static void stop_reclaim_thread(void)
{
	int ret;
	void *tret;

	STORE_SHARED(exit_reclaim, 1);
	ret = pthread_join(tid_reclaim, &tret);
	assert(!ret);
}

void rcu_reclaim_register_thread(void)
{
	int reclaimers;

	internal_urcu_lock(&reclaim_thread_mutex);
	internal_urcu_lock(&urcu_reclaim_mutex);
	reclaim_queue.q = malloc(sizeof(void *) * RECLAIM_QUEUE_SIZE);
	rcu_add_reclaimer(pthread_self());
	reclaimers = num_reclaimers;
	internal_urcu_unlock(&urcu_reclaim_mutex);

	if (reclaimers == 1)
		start_reclaim_thread();
	internal_urcu_unlock(&reclaim_thread_mutex);
}

void rcu_reclaim_unregister_thread(void)
{
	int reclaimers;

	internal_urcu_lock(&reclaim_thread_mutex);
	internal_urcu_lock(&urcu_reclaim_mutex);
	rcu_remove_reclaimer(pthread_self());
	_rcu_reclaim_barrier_thread();
	free(reclaim_queue.q);
	reclaim_queue.q = NULL;
	reclaimers = num_reclaimers;
	internal_urcu_unlock(&urcu_reclaim_mutex);

	if (reclaimers == 0)
		stop_reclaim_thread();
	internal_urcu_unlock(&reclaim_thread_mutex);
}

void urcu_reclaim_exit(void)
{
	free(registry);
}
