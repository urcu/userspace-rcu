/*
 * urcu-qsbr.c
 *
 * Userspace RCU QSBR library
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

#define BUILD_QSBR_LIB
#include "urcu-qsbr-static.h"
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include "urcu-qsbr.h"

void __attribute__((destructor)) rcu_exit(void);

static pthread_mutex_t rcu_gp_lock = PTHREAD_MUTEX_INITIALIZER;

int gp_futex;

/*
 * Global grace period counter.
 */
unsigned long rcu_gp_ctr = RCU_GP_ONLINE;

/*
 * Written to only by each individual reader. Read by both the reader and the
 * writers.
 */
struct rcu_reader __thread rcu_reader;

#ifdef DEBUG_YIELD
unsigned int yield_active;
unsigned int __thread rand_yield;
#endif

static LIST_HEAD(registry);

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
 * synchronize_rcu() waiting. Single thread.
 */
static void wait_gp(void)
{
	/* Read reader_gp before read futex */
	smp_rmb();
	if (uatomic_read(&gp_futex) == -1)
		futex_noasync(&gp_futex, FUTEX_WAIT, -1,
		      NULL, NULL, 0);
}

static void update_counter_and_wait(void)
{
	LIST_HEAD(qsreaders);
	int wait_loops = 0;
	struct rcu_reader *index, *tmp;

#if (BITS_PER_LONG < 64)
	/* Switch parity: 0 -> 1, 1 -> 0 */
	STORE_SHARED(rcu_gp_ctr, rcu_gp_ctr ^ RCU_GP_CTR);
#else	/* !(BITS_PER_LONG < 64) */
	/* Increment current G.P. */
	STORE_SHARED(rcu_gp_ctr, rcu_gp_ctr + RCU_GP_CTR);
#endif	/* !(BITS_PER_LONG < 64) */

	/*
	 * Must commit rcu_gp_ctr update to memory before waiting for quiescent
	 * state. Failure to do so could result in the writer waiting forever
	 * while new readers are always accessing data (no progress). Enforce
	 * compiler-order of store to rcu_gp_ctr before load rcu_reader ctr.
	 */
	barrier();

	/*
	 * Adding a smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	smp_mb();

	/*
	 * Wait for each thread rcu_reader_qs_gp count to become 0.
	 */
	for (;;) {
		wait_loops++;
		if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS) {
			uatomic_dec(&gp_futex);
			/* Write futex before read reader_gp */
			smp_mb();
		}

		list_for_each_entry_safe(index, tmp, &registry, node) {
			if (!rcu_gp_ongoing(&index->ctr))
				list_move(&index->node, &qsreaders);
		}

		if (list_empty(&registry)) {
			if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS) {
				/* Read reader_gp before write futex */
				smp_mb();
				uatomic_set(&gp_futex, 0);
			}
			break;
		} else {
			if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS) {
				wait_gp();
			} else {
#ifndef HAS_INCOHERENT_CACHES
				cpu_relax();
#else /* #ifndef HAS_INCOHERENT_CACHES */
				smp_mb();
#endif /* #else #ifndef HAS_INCOHERENT_CACHES */
			}
		}
	}
	/* put back the reader list in the registry */
	list_splice(&qsreaders, &registry);
}

/*
 * Using a two-subphases algorithm for architectures with smaller than 64-bit
 * long-size to ensure we do not encounter an overflow bug.
 */

#if (BITS_PER_LONG < 64)
void synchronize_rcu(void)
{
	unsigned long was_online;

	was_online = rcu_reader.ctr;

	/* All threads should read qparity before accessing data structure
	 * where new ptr points to.
	 */
	/* Write new ptr before changing the qparity */
	smp_mb();

	/*
	 * Mark the writer thread offline to make sure we don't wait for
	 * our own quiescent state. This allows using synchronize_rcu() in
	 * threads registered as readers.
	 */
	if (was_online)
		STORE_SHARED(rcu_reader.ctr, 0);

	mutex_lock(&rcu_gp_lock);

	if (list_empty(&registry))
		goto out;

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	update_counter_and_wait();	/* 0 -> 1, wait readers in parity 0 */

	/*
	 * Must finish waiting for quiescent state for parity 0 before
	 * committing next rcu_gp_ctr update to memory. Failure to do so could
	 * result in the writer waiting forever while new readers are always
	 * accessing data (no progress).  Enforce compiler-order of load
	 * rcu_reader ctr before store to rcu_gp_ctr.
	 */
	barrier();

	/*
	 * Adding a smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	smp_mb();

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	update_counter_and_wait();	/* 1 -> 0, wait readers in parity 1 */
out:
	mutex_unlock(&rcu_gp_lock);

	/*
	 * Finish waiting for reader threads before letting the old ptr being
	 * freed.
	 */
	if (was_online)
		_STORE_SHARED(rcu_reader.ctr, LOAD_SHARED(rcu_gp_ctr));
	smp_mb();
}
#else /* !(BITS_PER_LONG < 64) */
void synchronize_rcu(void)
{
	unsigned long was_online;

	was_online = rcu_reader.ctr;

	/*
	 * Mark the writer thread offline to make sure we don't wait for
	 * our own quiescent state. This allows using synchronize_rcu() in
	 * threads registered as readers.
	 */
	smp_mb();
	if (was_online)
		STORE_SHARED(rcu_reader.ctr, 0);

	mutex_lock(&rcu_gp_lock);
	if (list_empty(&registry))
		goto out;
	update_counter_and_wait();
out:
	mutex_unlock(&rcu_gp_lock);

	if (was_online)
		_STORE_SHARED(rcu_reader.ctr, LOAD_SHARED(rcu_gp_ctr));
	smp_mb();
}
#endif  /* !(BITS_PER_LONG < 64) */

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

void rcu_quiescent_state(void)
{
	_rcu_quiescent_state();
}

void rcu_thread_offline(void)
{
	_rcu_thread_offline();
}

void rcu_thread_online(void)
{
	_rcu_thread_online();
}

void rcu_register_thread(void)
{
	rcu_reader.tid = pthread_self();
	assert(rcu_reader.ctr == 0);

	mutex_lock(&rcu_gp_lock);
	list_add(&rcu_reader.node, &registry);
	mutex_unlock(&rcu_gp_lock);
	_rcu_thread_online();
}

void rcu_unregister_thread(void)
{
	/*
	 * We have to make the thread offline otherwise we end up dealocking
	 * with a waiting writer.
	 */
	_rcu_thread_offline();
	mutex_lock(&rcu_gp_lock);
	list_del(&rcu_reader.node);
	mutex_unlock(&rcu_gp_lock);
}

void rcu_exit(void)
{
	assert(list_empty(&registry));
}
