#ifndef _URCU_STATIC_H
#define _URCU_STATIC_H

/*
 * urcu-static.h
 *
 * Userspace RCU header.
 *
 * TO BE INCLUDED ONLY IN CODE THAT IS TO BE RECOMPILED ON EACH LIBURCU
 * RELEASE. See urcu.h for linking dynamically with the userspace rcu library.
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

#include <stdlib.h>
#include <pthread.h>
#include <unistd.h>
#include <stdint.h>

#include <urcu/compiler.h>
#include <urcu/arch.h>
#include <urcu/system.h>
#include <urcu/uatomic.h>
#include <urcu/list.h>
#include <urcu/futex.h>
#include <urcu/tls-compat.h>

#ifdef __cplusplus
extern "C" {
#endif 

/* Default is RCU_MEMBARRIER */
#if !defined(RCU_MEMBARRIER) && !defined(RCU_MB) && !defined(RCU_SIGNAL)
#define RCU_MEMBARRIER
#endif

/*
 * RCU_MEMBARRIER is only possibly available on Linux. Fallback to RCU_MB
 * otherwise.
 */
#if !defined(__linux__) && defined(RCU_MEMBARRIER)
#undef RCU_MEMBARRIER
#define RCU_MB
#endif

#ifdef RCU_MEMBARRIER
#include <syscall.h>

/* If the headers do not support SYS_membarrier, statically use RCU_MB */
#ifdef SYS_membarrier
# define MEMBARRIER_EXPEDITED		(1 << 0)
# define MEMBARRIER_DELAYED		(1 << 1)
# define MEMBARRIER_QUERY		(1 << 16)
# define membarrier(...)		syscall(SYS_membarrier, __VA_ARGS__)
#else
# undef RCU_MEMBARRIER
# define RCU_MB
#endif
#endif

/*
 * This code section can only be included in LGPL 2.1 compatible source code.
 * See below for the function call wrappers which can be used in code meant to
 * be only linked with the Userspace RCU library. This comes with a small
 * performance degradation on the read-side due to the added function calls.
 * This is required to permit relinking with newer versions of the library.
 */

/*
 * The signal number used by the RCU library can be overridden with
 * -DSIGRCU= when compiling the library.
 * Provide backward compatibility for liburcu 0.3.x SIGURCU.
 */
#ifdef SIGURCU
#define SIGRCU SIGURCU
#endif

#ifndef SIGRCU
#define SIGRCU SIGUSR1
#endif

#ifdef DEBUG_RCU
#define rcu_assert(args...)	assert(args)
#else
#define rcu_assert(args...)
#endif

#ifdef DEBUG_YIELD
#include <sched.h>
#include <time.h>
#include <pthread.h>
#include <unistd.h>

#define YIELD_READ 	(1 << 0)
#define YIELD_WRITE	(1 << 1)

/*
 * Updates with RCU_SIGNAL are much slower. Account this in the delay.
 */
#ifdef RCU_SIGNAL
/* maximum sleep delay, in us */
#define MAX_SLEEP 30000
#else
#define MAX_SLEEP 50
#endif

extern unsigned int yield_active;
extern DECLARE_URCU_TLS(unsigned int, rand_yield);

static inline void debug_yield_read(void)
{
	if (yield_active & YIELD_READ)
		if (rand_r(&URCU_TLS(rand_yield)) & 0x1)
			usleep(rand_r(&URCU_TLS(rand_yield)) % MAX_SLEEP);
}

static inline void debug_yield_write(void)
{
	if (yield_active & YIELD_WRITE)
		if (rand_r(&URCU_TLS(rand_yield)) & 0x1)
			usleep(rand_r(&URCU_TLS(rand_yield)) % MAX_SLEEP);
}

static inline void debug_yield_init(void)
{
	URCU_TLS(rand_yield) = time(NULL) ^ (unsigned long) pthread_self();
}
#else
static inline void debug_yield_read(void)
{
}

static inline void debug_yield_write(void)
{
}

static inline void debug_yield_init(void)
{

}
#endif

/*
 * RCU memory barrier broadcast group. Currently, only broadcast to all process
 * threads is supported (group 0).
 *
 * Slave barriers are only guaranteed to be ordered wrt master barriers.
 *
 * The pair ordering is detailed as (O: ordered, X: not ordered) :
 *               slave  master
 *        slave    X      O
 *        master   O      O
 */

#define MB_GROUP_ALL		0
#define RCU_MB_GROUP		MB_GROUP_ALL

#ifdef RCU_MEMBARRIER
extern int has_sys_membarrier;

static inline void smp_mb_slave(int group)
{
	if (caa_likely(has_sys_membarrier))
		cmm_barrier();
	else
		cmm_smp_mb();
}
#endif

#ifdef RCU_MB
static inline void smp_mb_slave(int group)
{
	cmm_smp_mb();
}
#endif

#ifdef RCU_SIGNAL
static inline void smp_mb_slave(int group)
{
	cmm_barrier();
}
#endif

/*
 * The trick here is that RCU_GP_CTR_PHASE must be a multiple of 8 so we can use
 * a full 8-bits, 16-bits or 32-bits bitmask for the lower order bits.
 */
#define RCU_GP_COUNT		(1UL << 0)
/* Use the amount of bits equal to half of the architecture long size */
#define RCU_GP_CTR_PHASE	(1UL << (sizeof(unsigned long) << 2))
#define RCU_GP_CTR_NEST_MASK	(RCU_GP_CTR_PHASE - 1)

/*
 * Global quiescent period counter with low-order bits unused.
 * Using a int rather than a char to eliminate false register dependencies
 * causing stalls on some architectures.
 */
extern unsigned long rcu_gp_ctr;

struct rcu_reader {
	/* Data used by both reader and synchronize_rcu() */
	unsigned long ctr;
	char need_mb;
	/* Data used for registry */
	struct cds_list_head node __attribute__((aligned(CAA_CACHE_LINE_SIZE)));
	pthread_t tid;
};

extern DECLARE_URCU_TLS(struct rcu_reader, rcu_reader);

extern int32_t gp_futex;

/*
 * Wake-up waiting synchronize_rcu(). Called from many concurrent threads.
 */
static inline void wake_up_gp(void)
{
	if (caa_unlikely(uatomic_read(&gp_futex) == -1)) {
		uatomic_set(&gp_futex, 0);
		futex_async(&gp_futex, FUTEX_WAKE, 1,
		      NULL, NULL, 0);
	}
}

static inline int rcu_gp_ongoing(unsigned long *ctr)
{
	unsigned long v;

	/*
	 * Make sure both tests below are done on the same version of *value
	 * to insure consistency.
	 */
	v = CMM_LOAD_SHARED(*ctr);
	return (v & RCU_GP_CTR_NEST_MASK) &&
		 ((v ^ rcu_gp_ctr) & RCU_GP_CTR_PHASE);
}

/*
 * Helper for _rcu_read_lock().  The format of rcu_gp_ctr (as well as
 * the per-thread rcu_reader.ctr) has the upper bits containing a count of
 * _rcu_read_lock() nesting, and a lower-order bit that contains either zero
 * or RCU_GP_CTR_PHASE.  The smp_mb_slave() ensures that the accesses in
 * _rcu_read_lock() happen before the subsequent read-side critical section.
 */
static inline void _rcu_read_lock_update(unsigned long tmp)
{
	if (caa_likely(!(tmp & RCU_GP_CTR_NEST_MASK))) {
		_CMM_STORE_SHARED(URCU_TLS(rcu_reader).ctr, _CMM_LOAD_SHARED(rcu_gp_ctr));
		smp_mb_slave(RCU_MB_GROUP);
	} else
		_CMM_STORE_SHARED(URCU_TLS(rcu_reader).ctr, tmp + RCU_GP_COUNT);
}

/*
 * Enter an RCU read-side critical section.
 *
 * The first cmm_barrier() call ensures that the compiler does not reorder
 * the body of _rcu_read_lock() with a mutex.
 *
 * This function and its helper are both less than 10 lines long.  The
 * intent is that this function meets the 10-line criterion in LGPL,
 * allowing this function to be invoked directly from non-LGPL code.
 */
static inline void _rcu_read_lock(void)
{
	unsigned long tmp;

	cmm_barrier();
	tmp = URCU_TLS(rcu_reader).ctr;
	_rcu_read_lock_update(tmp);
}

/*
 * This is a helper function for _rcu_read_unlock().
 *
 * The first smp_mb_slave() call ensures that the critical section is
 * seen to precede the store to rcu_reader.ctr.
 * The second smp_mb_slave() call ensures that we write to rcu_reader.ctr
 * before reading the update-side futex.
 */
static inline void _rcu_read_unlock_update_and_wakeup(unsigned long tmp)
{
	if (caa_likely((tmp & RCU_GP_CTR_NEST_MASK) == RCU_GP_COUNT)) {
		smp_mb_slave(RCU_MB_GROUP);
		_CMM_STORE_SHARED(URCU_TLS(rcu_reader).ctr, URCU_TLS(rcu_reader).ctr - RCU_GP_COUNT);
		smp_mb_slave(RCU_MB_GROUP);
		wake_up_gp();
	} else
		_CMM_STORE_SHARED(URCU_TLS(rcu_reader).ctr, URCU_TLS(rcu_reader).ctr - RCU_GP_COUNT);
}

/*
 * Exit an RCU read-side crtical section.  Both this function and its
 * helper are smaller than 10 lines of code, and are intended to be
 * usable by non-LGPL code, as called out in LGPL.
 */
static inline void _rcu_read_unlock(void)
{
	unsigned long tmp;

	tmp = URCU_TLS(rcu_reader).ctr;
	_rcu_read_unlock_update_and_wakeup(tmp);
	cmm_barrier();	/* Ensure the compiler does not reorder us with mutex */
}

#ifdef __cplusplus
}
#endif

#endif /* _URCU_STATIC_H */
