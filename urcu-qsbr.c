/*
 * urcu.c
 *
 * Userspace RCU library
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
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
 *
 * IBM's contributions to this file may be relicensed under LGPLv2 or later.
 */

#include <stdio.h>
#include <pthread.h>
#include <signal.h>
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <poll.h>

#include "urcu-qsbr.h"
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
//#include "urcu.h"

pthread_mutex_t urcu_mutex = PTHREAD_MUTEX_INITIALIZER;

/*
 * Global grace period counter.
 */
long urcu_gp_ctr = 0;

/*
 * Written to only by each individual reader. Read by both the reader and the
 * writers.
 */
long __thread rcu_reader_qs_gp;

/* Thread IDs of registered readers */
#define INIT_NUM_THREADS 4

struct reader_registry {
	pthread_t tid;
	long *rcu_reader_qs_gp;
	char *need_mb;
};

#ifdef DEBUG_YIELD
unsigned int yield_active;
unsigned int __thread rand_yield;
#endif

static struct reader_registry *registry;
static char __thread need_mb;
static int num_readers, alloc_readers;

void internal_urcu_lock(void)
{
	int ret;

#ifndef DISTRUST_SIGNALS_EXTREME
	ret = pthread_mutex_lock(&urcu_mutex);
	if (ret) {
		perror("Error in pthread mutex lock");
		exit(-1);
	}
#else /* #ifndef DISTRUST_SIGNALS_EXTREME */
	while ((ret = pthread_mutex_trylock(&urcu_mutex)) != 0) {
		if (ret != EBUSY && ret != EINTR) {
			printf("ret = %d, errno = %d\n", ret, errno);
			perror("Error in pthread mutex lock");
			exit(-1);
		}
		if (need_mb) {
			smp_mb();
			need_mb = 0;
			smp_mb();
		}
		poll(NULL,0,10);
	}
#endif /* #else #ifndef DISTRUST_SIGNALS_EXTREME */
}

void internal_urcu_unlock(void)
{
	int ret;

	ret = pthread_mutex_unlock(&urcu_mutex);
	if (ret) {
		perror("Error in pthread mutex unlock");
		exit(-1);
	}
}

#ifdef HAS_INCOHERENT_CACHES
static void force_mb_single_thread(struct reader_registry *index)
{
	smp_mb();
}
#endif /* #ifdef HAS_INCOHERENT_CACHES */

static void force_mb_all_threads(void)
{
	smp_mb();
}

void wait_for_quiescent_state(void)
{
	struct reader_registry *index;

	if (!registry)
		return;
	/*
	 * Wait for each thread rcu_reader_qs_gp count to become 0.
	 */
	for (index = registry; index < registry + num_readers; index++) {
#ifndef HAS_INCOHERENT_CACHES
		while (rcu_gp_ongoing(index->rcu_reader_qs_gp) &&
		       (*index->rcu_reader_qs_gp - urcu_gp_ctr < 0))
			cpu_relax();
#else /* #ifndef HAS_INCOHERENT_CACHES */
		int wait_loops = 0;
		/*
		 * BUSY-LOOP. Force the reader thread to commit its
		 * rcu_reader_qs_gp update to memory if we wait for too long.
		 */
		while (rcu_gp_ongoing(index->rcu_reader_qs_gp) &&
		       (*index->rcu_reader_qs_gp - urcu_gp_ctr < 0)) {
			if (wait_loops++ == KICK_READER_LOOPS) {
				force_mb_single_thread(index);
				wait_loops = 0;
			} else {
				cpu_relax();
			}
		}
#endif /* #else #ifndef HAS_INCOHERENT_CACHES */
	}
}

void synchronize_rcu(void)
{
	internal_urcu_lock();
	force_mb_all_threads();
	urcu_gp_ctr += 2;
	wait_for_quiescent_state();
	force_mb_all_threads();
	internal_urcu_unlock();
}

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

void rcu_read_lock(void)
{
	_rcu_read_lock();
}

void rcu_read_unlock(void)
{
	_rcu_read_unlock();
}

void *rcu_dereference(void *p)
{
	return _rcu_dereference(p);
}

void *rcu_assign_pointer_sym(void **p, void *v)
{
	wmb();
	return STORE_SHARED(p, v);
}

void *rcu_xchg_pointer_sym(void **p, void *v)
{
	wmb();
	return xchg(p, v);
}

void *rcu_publish_content_sym(void **p, void *v)
{
	void *oldptr;

	oldptr = _rcu_xchg_pointer(p, v);
	synchronize_rcu();
	return oldptr;
}

static void rcu_add_reader(pthread_t id)
{
	struct reader_registry *oldarray;

	if (!registry) {
		alloc_readers = INIT_NUM_THREADS;
		num_readers = 0;
		registry =
			malloc(sizeof(struct reader_registry) * alloc_readers);
	}
	if (alloc_readers < num_readers + 1) {
		oldarray = registry;
		registry = malloc(sizeof(struct reader_registry)
				* (alloc_readers << 1));
		memcpy(registry, oldarray,
			sizeof(struct reader_registry) * alloc_readers);
		alloc_readers <<= 1;
		free(oldarray);
	}
	registry[num_readers].tid = id;
	/* reference to the TLS of _this_ reader thread. */
	registry[num_readers].rcu_reader_qs_gp = &rcu_reader_qs_gp;
	registry[num_readers].need_mb = &need_mb;
	num_readers++;
}

/*
 * Never shrink (implementation limitation).
 * This is O(nb threads). Eventually use a hash table.
 */
static void rcu_remove_reader(pthread_t id)
{
	struct reader_registry *index;

	assert(registry != NULL);
	for (index = registry; index < registry + num_readers; index++) {
		if (pthread_equal(index->tid, id)) {
			memcpy(index, &registry[num_readers - 1],
				sizeof(struct reader_registry));
			registry[num_readers - 1].tid = 0;
			registry[num_readers - 1].rcu_reader_qs_gp = NULL;
			num_readers--;
			return;
		}
	}
	/* Hrm not found, forgot to register ? */
	assert(0);
}

void rcu_register_thread(void)
{
	internal_urcu_lock();
	rcu_add_reader(pthread_self());
	internal_urcu_unlock();
	_rcu_thread_online();
}

void rcu_unregister_thread(void)
{
	/*
	 * We have to make the thread offline otherwise we end up dealocking
	 * with a waiting writer.
	 */
	_rcu_thread_offline();
	internal_urcu_lock();
	rcu_remove_reader(pthread_self());
	internal_urcu_unlock();
}
