/*
 * urcu.c
 *
 * Userspace RCU library
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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

#define _BSD_SOURCE
#define _GNU_SOURCE
#define _LGPL_SOURCE
#include <stdio.h>
#include <pthread.h>
#include <signal.h>
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <poll.h>

#include "urcu/wfqueue.h"
#include "urcu/map/urcu.h"
#include "urcu/static/urcu.h"
#include "urcu-pointer.h"

/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#undef _LGPL_SOURCE
#include "urcu.h"
#define _LGPL_SOURCE

/*
 * If a reader is really non-cooperative and refuses to commit its
 * rcu_active_readers count to memory (there is no barrier in the reader
 * per-se), kick it after a few loops waiting for it.
 */
#define KICK_READER_LOOPS 10000

/*
 * Active attempts to check for reader Q.S. before calling futex().
 */
#define RCU_QS_ACTIVE_ATTEMPTS 100

#ifdef RCU_MEMBARRIER
static int init_done;
int has_sys_membarrier;

void __attribute__((constructor)) rcu_init(void);
#endif

#ifdef RCU_MB
void rcu_init(void)
{
}
#endif

#ifdef RCU_SIGNAL
static int init_done;

void __attribute__((constructor)) rcu_init(void);
void __attribute__((destructor)) rcu_exit(void);
#endif

static pthread_mutex_t rcu_gp_lock = PTHREAD_MUTEX_INITIALIZER;

int32_t gp_futex;

/*
 * Global grace period counter.
 * Contains the current RCU_GP_CTR_PHASE.
 * Also has a RCU_GP_COUNT of 1, to accelerate the reader fast path.
 * Written to only by writer with mutex taken. Read by both writer and readers.
 */
unsigned long rcu_gp_ctr = RCU_GP_COUNT;

/*
 * Written to only by each individual reader. Read by both the reader and the
 * writers.
 */
struct rcu_reader __thread rcu_reader;

#ifdef DEBUG_YIELD
unsigned int yield_active;
unsigned int __thread rand_yield;
#endif

static CDS_LIST_HEAD(registry);

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
		if (CMM_LOAD_SHARED(rcu_reader.need_mb)) {
			cmm_smp_mb();
			_CMM_STORE_SHARED(rcu_reader.need_mb, 0);
			cmm_smp_mb();
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

#ifdef RCU_MEMBARRIER
static void smp_mb_master(int group)
{
	if (likely(has_sys_membarrier))
		membarrier(MEMBARRIER_EXPEDITED);
	else
		cmm_smp_mb();
}
#endif

#ifdef RCU_MB
static void smp_mb_master(int group)
{
	cmm_smp_mb();
}
#endif

#ifdef RCU_SIGNAL
static void force_mb_all_readers(void)
{
	struct rcu_reader *index;

	/*
	 * Ask for each threads to execute a cmm_smp_mb() so we can consider the
	 * compiler barriers around rcu read lock as real memory barriers.
	 */
	if (cds_list_empty(&registry))
		return;
	/*
	 * pthread_kill has a cmm_smp_mb(). But beware, we assume it performs
	 * a cache flush on architectures with non-coherent cache. Let's play
	 * safe and don't assume anything : we use cmm_smp_mc() to make sure the
	 * cache flush is enforced.
	 */
	cds_list_for_each_entry(index, &registry, node) {
		CMM_STORE_SHARED(index->need_mb, 1);
		pthread_kill(index->tid, SIGRCU);
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
	cds_list_for_each_entry(index, &registry, node) {
		while (CMM_LOAD_SHARED(index->need_mb)) {
			pthread_kill(index->tid, SIGRCU);
			poll(NULL, 0, 1);
		}
	}
	cmm_smp_mb();	/* read ->need_mb before ending the barrier */
}

static void smp_mb_master(int group)
{
	force_mb_all_readers();
}
#endif /* #ifdef RCU_SIGNAL */

/*
 * synchronize_rcu() waiting. Single thread.
 */
static void wait_gp(void)
{
	/* Read reader_gp before read futex */
	smp_mb_master(RCU_MB_GROUP);
	if (uatomic_read(&gp_futex) == -1)
		futex_async(&gp_futex, FUTEX_WAIT, -1,
		      NULL, NULL, 0);
}

void update_counter_and_wait(void)
{
	CDS_LIST_HEAD(qsreaders);
	int wait_loops = 0;
	struct rcu_reader *index, *tmp;

	/* Switch parity: 0 -> 1, 1 -> 0 */
	CMM_STORE_SHARED(rcu_gp_ctr, rcu_gp_ctr ^ RCU_GP_CTR_PHASE);

	/*
	 * Must commit rcu_gp_ctr update to memory before waiting for quiescent
	 * state. Failure to do so could result in the writer waiting forever
	 * while new readers are always accessing data (no progress). Enforce
	 * compiler-order of store to rcu_gp_ctr before load rcu_reader ctr.
	 */
	cmm_barrier();

	/*
	 *
	 * Adding a cmm_smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	cmm_smp_mb();

	/*
	 * Wait for each thread rcu_reader.ctr count to become 0.
	 */
	for (;;) {
		wait_loops++;
		if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS) {
			uatomic_dec(&gp_futex);
			/* Write futex before read reader_gp */
			smp_mb_master(RCU_MB_GROUP);
		}

		cds_list_for_each_entry_safe(index, tmp, &registry, node) {
			if (!rcu_gp_ongoing(&index->ctr))
				cds_list_move(&index->node, &qsreaders);
		}

#ifndef HAS_INCOHERENT_CACHES
		if (cds_list_empty(&registry)) {
			if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS) {
				/* Read reader_gp before write futex */
				smp_mb_master(RCU_MB_GROUP);
				uatomic_set(&gp_futex, 0);
			}
			break;
		} else {
			if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS)
				wait_gp();
			else
				caa_cpu_relax();
		}
#else /* #ifndef HAS_INCOHERENT_CACHES */
		/*
		 * BUSY-LOOP. Force the reader thread to commit its
		 * rcu_reader.ctr update to memory if we wait for too long.
		 */
		if (cds_list_empty(&registry)) {
			if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS) {
				/* Read reader_gp before write futex */
				smp_mb_master(RCU_MB_GROUP);
				uatomic_set(&gp_futex, 0);
			}
			break;
		} else {
			switch (wait_loops) {
			case RCU_QS_ACTIVE_ATTEMPTS:
				wait_gp();
				break; /* only escape switch */
			case KICK_READER_LOOPS:
				smp_mb_master(RCU_MB_GROUP);
				wait_loops = 0;
				break; /* only escape switch */
			default:
				caa_cpu_relax();
			}
		}
#endif /* #else #ifndef HAS_INCOHERENT_CACHES */
	}
	/* put back the reader list in the registry */
	cds_list_splice(&qsreaders, &registry);
}

void synchronize_rcu(void)
{
	mutex_lock(&rcu_gp_lock);

	if (cds_list_empty(&registry))
		goto out;

	/* All threads should read qparity before accessing data structure
	 * where new ptr points to. Must be done within rcu_gp_lock because it
	 * iterates on reader threads.*/
	/* Write new ptr before changing the qparity */
	smp_mb_master(RCU_MB_GROUP);

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
	cmm_barrier();

	/*
	 * Adding a cmm_smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	cmm_smp_mb();

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	update_counter_and_wait();	/* 1 -> 0, wait readers in parity 1 */

	/* Finish waiting for reader threads before letting the old ptr being
	 * freed. Must be done within rcu_gp_lock because it iterates on reader
	 * threads. */
	smp_mb_master(RCU_MB_GROUP);
out:
	mutex_unlock(&rcu_gp_lock);
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
	rcu_reader.tid = pthread_self();
	assert(rcu_reader.need_mb == 0);
	assert(!(rcu_reader.ctr & RCU_GP_CTR_NEST_MASK));

	mutex_lock(&rcu_gp_lock);
	rcu_init();	/* In case gcc does not support constructor attribute */
	cds_list_add(&rcu_reader.node, &registry);
	mutex_unlock(&rcu_gp_lock);
}

void rcu_unregister_thread(void)
{
	mutex_lock(&rcu_gp_lock);
	cds_list_del(&rcu_reader.node);
	mutex_unlock(&rcu_gp_lock);
}

#ifdef RCU_MEMBARRIER
void rcu_init(void)
{
	if (init_done)
		return;
	init_done = 1;
	if (!membarrier(MEMBARRIER_EXPEDITED | MEMBARRIER_QUERY))
		has_sys_membarrier = 1;
}
#endif

#ifdef RCU_SIGNAL
static void sigrcu_handler(int signo, siginfo_t *siginfo, void *context)
{
	/*
	 * Executing this cmm_smp_mb() is the only purpose of this signal handler.
	 * It punctually promotes cmm_barrier() into cmm_smp_mb() on every thread it is
	 * executed on.
	 */
	cmm_smp_mb();
	_CMM_STORE_SHARED(rcu_reader.need_mb, 0);
	cmm_smp_mb();
}

/*
 * rcu_init constructor. Called when the library is linked, but also when
 * reader threads are calling rcu_register_thread().
 * Should only be called by a single thread at a given time. This is ensured by
 * holing the rcu_gp_lock from rcu_register_thread() or by running at library
 * load time, which should not be executed by multiple threads nor concurrently
 * with rcu_register_thread() anyway.
 */
void rcu_init(void)
{
	struct sigaction act;
	int ret;

	if (init_done)
		return;
	init_done = 1;

	act.sa_sigaction = sigrcu_handler;
	act.sa_flags = SA_SIGINFO | SA_RESTART;
	sigemptyset(&act.sa_mask);
	ret = sigaction(SIGRCU, &act, NULL);
	if (ret) {
		perror("Error in sigaction");
		exit(-1);
	}
}

void rcu_exit(void)
{
	struct sigaction act;
	int ret;

	ret = sigaction(SIGRCU, NULL, &act);
	if (ret) {
		perror("Error in sigaction");
		exit(-1);
	}
	assert(act.sa_sigaction == sigrcu_handler);
	assert(cds_list_empty(&registry));
}

#endif /* #ifdef RCU_SIGNAL */

#include "urcu-call-rcu-impl.h"
#include "urcu-defer-impl.h"
