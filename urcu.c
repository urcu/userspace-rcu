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

#include "urcu-static.h"
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include "urcu.h"

#ifndef URCU_MB
static int init_done;

void __attribute__((constructor)) urcu_init(void);
void __attribute__((destructor)) urcu_exit(void);
#else
void urcu_init(void)
{
}
#endif

static pthread_mutex_t urcu_mutex = PTHREAD_MUTEX_INITIALIZER;

int gp_futex;

/*
 * Global grace period counter.
 * Contains the current RCU_GP_CTR_BIT.
 * Also has a RCU_GP_COUNT of 1, to accelerate the reader fast path.
 * Written to only by writer with mutex taken. Read by both writer and readers.
 */
long urcu_gp_ctr = RCU_GP_COUNT;

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
		if (urcu_reader.need_mb) {
			smp_mb();
			urcu_reader.need_mb = 0;
			smp_mb();
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
 * called with urcu_mutex held.
 */
static void switch_next_urcu_qparity(void)
{
	STORE_SHARED(urcu_gp_ctr, urcu_gp_ctr ^ RCU_GP_CTR_BIT);
}

#ifdef URCU_MB
#if 0 /* unused */
static void force_mb_single_thread(struct urcu_reader *index)
{
	smp_mb();
}
#endif //0

static void force_mb_all_threads(void)
{
	smp_mb();
}
#else /* #ifdef URCU_MB */
#if 0 /* unused */
static void force_mb_single_thread(struct urcu_reader *index)
{
	assert(!list_empty(&registry));
	/*
	 * pthread_kill has a smp_mb(). But beware, we assume it performs
	 * a cache flush on architectures with non-coherent cache. Let's play
	 * safe and don't assume anything : we use smp_mc() to make sure the
	 * cache flush is enforced.
	 */
	index->need_mb = 1;
	smp_mc();	/* write ->need_mb before sending the signals */
	pthread_kill(index->tid, SIGURCU);
	smp_mb();
	/*
	 * Wait for sighandler (and thus mb()) to execute on every thread.
	 * BUSY-LOOP.
	 */
	while (index->need_mb) {
		poll(NULL, 0, 1);
	}
	smp_mb();	/* read ->need_mb before ending the barrier */
}
#endif //0

static void force_mb_all_threads(void)
{
	struct urcu_reader *index;

	/*
	 * Ask for each threads to execute a smp_mb() so we can consider the
	 * compiler barriers around rcu read lock as real memory barriers.
	 */
	if (list_empty(&registry))
		return;
	/*
	 * pthread_kill has a smp_mb(). But beware, we assume it performs
	 * a cache flush on architectures with non-coherent cache. Let's play
	 * safe and don't assume anything : we use smp_mc() to make sure the
	 * cache flush is enforced.
	 */
	list_for_each_entry(index, &registry, head) {
		index->need_mb = 1;
		smp_mc();	/* write need_mb before sending the signal */
		pthread_kill(index->tid, SIGURCU);
	}
	/*
	 * Wait for sighandler (and thus mb()) to execute on every thread.
	 *
	 * Note that the pthread_kill() will never be executed on systems
	 * that correctly deliver signals in a timely manner.  However, it
	 * is not uncommon for kernels to have bugs that can result in
	 * lost or unduly delayed signals.
	 *
	 * If you are seeing the below pthread_kill() executing much at
	 * all, we suggest testing the underlying kernel and filing the
	 * relevant bug report.  For Linux kernels, we recommend getting
	 * the Linux Test Project (LTP).
	 */
	list_for_each_entry(index, &registry, head) {
		while (index->need_mb) {
			pthread_kill(index->tid, SIGURCU);
			poll(NULL, 0, 1);
		}
	}
	smp_mb();	/* read ->need_mb before ending the barrier */
}
#endif /* #else #ifdef URCU_MB */

/*
 * synchronize_rcu() waiting. Single thread.
 */
static void wait_gp(void)
{
	/* Read reader_gp before read futex */
	force_mb_all_threads();
	if (uatomic_read(&gp_futex) == -1)
		futex_async(&gp_futex, FUTEX_WAIT, -1,
		      NULL, NULL, 0);
}

void wait_for_quiescent_state(void)
{
	LIST_HEAD(qsreaders);
	int wait_loops = 0;
	struct urcu_reader *index, *tmp;

	if (list_empty(&registry))
		return;
	/*
	 * Wait for each thread urcu_reader.ctr count to become 0.
	 */
	for (;;) {
		wait_loops++;
		if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS) {
			uatomic_dec(&gp_futex);
			/* Write futex before read reader_gp */
			force_mb_all_threads();
		}

		list_for_each_entry_safe(index, tmp, &registry, head) {
			if (!rcu_old_gp_ongoing(&index->ctr))
				list_move(&index->head, &qsreaders);
		}

#ifndef HAS_INCOHERENT_CACHES
		if (list_empty(&registry)) {
			if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS) {
				/* Read reader_gp before write futex */
				force_mb_all_threads();
				uatomic_set(&gp_futex, 0);
			}
			break;
		} else {
			if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS)
				wait_gp();
			else
				cpu_relax();
		}
#else /* #ifndef HAS_INCOHERENT_CACHES */
		/*
		 * BUSY-LOOP. Force the reader thread to commit its
		 * urcu_reader.ctr update to memory if we wait for too long.
		 */
		if (list_empty(&registry)) {
			if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS) {
				/* Read reader_gp before write futex */
				force_mb_all_threads();
				uatomic_set(&gp_futex, 0);
			}
			break;
		} else {
			switch (wait_loops) {
			case RCU_QS_ACTIVE_ATTEMPTS:
				wait_gp();
				break; /* only escape switch */
			case KICK_READER_LOOPS:
				force_mb_all_threads();
				wait_loops = 0;
				break; /* only escape switch */
			default:
				cpu_relax();
			}
		}
#endif /* #else #ifndef HAS_INCOHERENT_CACHES */
	}
	/* put back the reader list in the registry */
	list_splice(&qsreaders, &registry);
}

void synchronize_rcu(void)
{
	internal_urcu_lock();

	/* All threads should read qparity before accessing data structure
	 * where new ptr points to. Must be done within internal_urcu_lock
	 * because it iterates on reader threads.*/
	/* Write new ptr before changing the qparity */
	force_mb_all_threads();

	switch_next_urcu_qparity();	/* 0 -> 1 */

	/*
	 * Must commit qparity update to memory before waiting for parity
	 * 0 quiescent state. Failure to do so could result in the writer
	 * waiting forever while new readers are always accessing data (no
	 * progress).
	 * Ensured by STORE_SHARED and LOAD_SHARED.
	 */

	/*
	 * Adding a smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	smp_mb();

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

	/*
	 * Adding a smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	smp_mb();

	switch_next_urcu_qparity();	/* 1 -> 0 */

	/*
	 * Must commit qparity update to memory before waiting for parity
	 * 1 quiescent state. Failure to do so could result in the writer
	 * waiting forever while new readers are always accessing data (no
	 * progress).
	 * Ensured by STORE_SHARED and LOAD_SHARED.
	 */

	/*
	 * Adding a smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	smp_mb();

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	wait_for_quiescent_state();	/* Wait readers in parity 1 */

	/* Finish waiting for reader threads before letting the old ptr being
	 * freed. Must be done within internal_urcu_lock because it iterates on
	 * reader threads. */
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

void rcu_register_thread(void)
{
	urcu_reader.tid = pthread_self();
	assert(urcu_reader.need_mb == 0);
	assert(urcu_reader.ctr == 0);

	internal_urcu_lock();
	urcu_init();	/* In case gcc does not support constructor attribute */
	list_add(&urcu_reader.head, &registry);
	internal_urcu_unlock();
}

void rcu_unregister_thread(void)
{
	internal_urcu_lock();
	list_del(&urcu_reader.head);
	internal_urcu_unlock();
}

#ifndef URCU_MB
static void sigurcu_handler(int signo, siginfo_t *siginfo, void *context)
{
	/*
	 * Executing this smp_mb() is the only purpose of this signal handler.
	 * It punctually promotes barrier() into smp_mb() on every thread it is
	 * executed on.
	 */
	smp_mb();
	urcu_reader.need_mb = 0;
	smp_mb();
}

/*
 * urcu_init constructor. Called when the library is linked, but also when
 * reader threads are calling rcu_register_thread().
 * Should only be called by a single thread at a given time. This is ensured by
 * holing the internal_urcu_lock() from rcu_register_thread() or by running at
 * library load time, which should not be executed by multiple threads nor
 * concurrently with rcu_register_thread() anyway.
 */
void urcu_init(void)
{
	struct sigaction act;
	int ret;

	if (init_done)
		return;
	init_done = 1;

	act.sa_sigaction = sigurcu_handler;
	act.sa_flags = SA_SIGINFO | SA_RESTART;
	sigemptyset(&act.sa_mask);
	ret = sigaction(SIGURCU, &act, NULL);
	if (ret) {
		perror("Error in sigaction");
		exit(-1);
	}
}

void urcu_exit(void)
{
	struct sigaction act;
	int ret;

	ret = sigaction(SIGURCU, NULL, &act);
	if (ret) {
		perror("Error in sigaction");
		exit(-1);
	}
	assert(act.sa_sigaction == sigurcu_handler);
	assert(list_empty(&registry));
}
#endif /* #ifndef URCU_MB */
