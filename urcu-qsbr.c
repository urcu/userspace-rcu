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

static pthread_mutex_t urcu_mutex = PTHREAD_MUTEX_INITIALIZER;

int gp_futex;

/*
 * Global grace period counter.
 */
unsigned long urcu_gp_ctr = RCU_GP_ONLINE;

/*
 * Written to only by each individual reader. Read by both the reader and the
 * writers.
 */
struct urcu_reader __thread urcu_reader;

#ifdef DEBUG_YIELD
unsigned int yield_active;
unsigned int __thread rand_yield;
#endif

static LIST_HEAD(registry);

static void internal_urcu_lock(void)
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
		poll(NULL,0,10);
	}
#endif /* #else #ifndef DISTRUST_SIGNALS_EXTREME */
}

static void internal_urcu_unlock(void)
{
	int ret;

	ret = pthread_mutex_unlock(&urcu_mutex);
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
		futex(&gp_futex, FUTEX_WAIT, -1,
		      NULL, NULL, 0);
}

static void wait_for_quiescent_state(void)
{
	LIST_HEAD(qsreaders);
	int wait_loops = 0;
	struct urcu_reader *index, *tmp;

	if (list_empty(&registry))
		return;
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

		list_for_each_entry_safe(index, tmp, &registry, head) {
			if (!rcu_gp_ongoing(&index->ctr))
				list_move(&index->head, &qsreaders);
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
/*
 * called with urcu_mutex held.
 */
static void switch_next_urcu_qparity(void)
{
	STORE_SHARED(urcu_gp_ctr, urcu_gp_ctr ^ RCU_GP_CTR);
}

void synchronize_rcu(void)
{
	unsigned long was_online;

	was_online = urcu_reader.ctr;

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
		STORE_SHARED(urcu_reader.ctr, 0);

	internal_urcu_lock();

	switch_next_urcu_qparity();	/* 0 -> 1 */

	/*
	 * Must commit qparity update to memory before waiting for parity
	 * 0 quiescent state. Failure to do so could result in the writer
	 * waiting forever while new readers are always accessing data (no
	 * progress).
	 * Ensured by STORE_SHARED and LOAD_SHARED.
	 */

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	wait_for_quiescent_state();	/* Wait readers in parity 0 */

	/*
	 * Must finish waiting for quiescent state for parity 0 before
	 * committing qparity update to memory. Failure to do so could result in
	 * the writer waiting forever while new readers are always accessing
	 * data (no progress).
	 * Ensured by STORE_SHARED and LOAD_SHARED.
	 */

	switch_next_urcu_qparity();	/* 1 -> 0 */

	/*
	 * Must commit qparity update to memory before waiting for parity
	 * 1 quiescent state. Failure to do so could result in the writer
	 * waiting forever while new readers are always accessing data (no
	 * progress).
	 * Ensured by STORE_SHARED and LOAD_SHARED.
	 */

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	wait_for_quiescent_state();	/* Wait readers in parity 1 */

	internal_urcu_unlock();

	/*
	 * Finish waiting for reader threads before letting the old ptr being
	 * freed.
	 */
	if (was_online)
		_STORE_SHARED(urcu_reader.ctr, LOAD_SHARED(urcu_gp_ctr));
	smp_mb();
}
#else /* !(BITS_PER_LONG < 64) */
void synchronize_rcu(void)
{
	unsigned long was_online;

	was_online = urcu_reader.ctr;

	/*
	 * Mark the writer thread offline to make sure we don't wait for
	 * our own quiescent state. This allows using synchronize_rcu() in
	 * threads registered as readers.
	 */
	smp_mb();
	if (was_online)
		STORE_SHARED(urcu_reader.ctr, 0);

	internal_urcu_lock();
	STORE_SHARED(urcu_gp_ctr, urcu_gp_ctr + RCU_GP_CTR);
	wait_for_quiescent_state();
	internal_urcu_unlock();

	if (was_online)
		_STORE_SHARED(urcu_reader.ctr, LOAD_SHARED(urcu_gp_ctr));
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
	urcu_reader.tid = pthread_self();
	assert(urcu_reader.ctr == 0);

	internal_urcu_lock();
	list_add(&urcu_reader.head, &registry);
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
	list_del(&urcu_reader.head);
	internal_urcu_unlock();
}

void rcu_exit(void)
{
	assert(list_empty(&registry));
}
