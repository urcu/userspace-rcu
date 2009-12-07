#ifndef _URCU_STATIC_H
#define _URCU_STATIC_H

/*
 * urcu-static.h
 *
 * Userspace RCU header.
 *
 * TO BE INCLUDED ONLY IN LGPL-COMPATIBLE CODE. See urcu.h for linking
 * dynamically with the userspace rcu library.
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

#include <stdlib.h>
#include <pthread.h>
#include <syscall.h>
#include <unistd.h>

#include <urcu/compiler.h>
#include <urcu/arch.h>
#include <urcu/system.h>
#include <urcu/uatomic_arch.h>
#include <urcu/list.h>
#include <urcu/urcu-futex.h>

#ifdef __cplusplus
extern "C" {
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
 * -DSIGURCU= when compiling the library.
 */
#ifndef SIGURCU
#define SIGURCU SIGUSR1
#endif

/*
 * If a reader is really non-cooperative and refuses to commit its
 * urcu_active_readers count to memory (there is no barrier in the reader
 * per-se), kick it after a few loops waiting for it.
 */
#define KICK_READER_LOOPS 10000

/*
 * Active attempts to check for reader Q.S. before calling futex().
 */
#define RCU_QS_ACTIVE_ATTEMPTS 100

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
 * Updates without URCU_MB are much slower. Account this in
 * the delay.
 */
#ifdef URCU_MB
/* maximum sleep delay, in us */
#define MAX_SLEEP 50
#else
#define MAX_SLEEP 30000
#endif

extern unsigned int yield_active;
extern unsigned int __thread rand_yield;

static inline void debug_yield_read(void)
{
	if (yield_active & YIELD_READ)
		if (rand_r(&rand_yield) & 0x1)
			usleep(rand_r(&rand_yield) % MAX_SLEEP);
}

static inline void debug_yield_write(void)
{
	if (yield_active & YIELD_WRITE)
		if (rand_r(&rand_yield) & 0x1)
			usleep(rand_r(&rand_yield) % MAX_SLEEP);
}

static inline void debug_yield_init(void)
{
	rand_yield = time(NULL) ^ pthread_self();
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

#ifdef URCU_MB
static inline void reader_barrier()
{
	smp_mb();
}
#else
static inline void reader_barrier()
{
	barrier();
}
#endif

/*
 * The trick here is that RCU_GP_CTR_BIT must be a multiple of 8 so we can use a
 * full 8-bits, 16-bits or 32-bits bitmask for the lower order bits.
 */
#define RCU_GP_COUNT		(1UL << 0)
/* Use the amount of bits equal to half of the architecture long size */
#define RCU_GP_CTR_BIT		(1UL << (sizeof(long) << 2))
#define RCU_GP_CTR_NEST_MASK	(RCU_GP_CTR_BIT - 1)

/*
 * Global quiescent period counter with low-order bits unused.
 * Using a int rather than a char to eliminate false register dependencies
 * causing stalls on some architectures.
 */
extern long urcu_gp_ctr;

struct urcu_reader {
	/* Data used by both reader and synchronize_rcu() */
	long ctr;
	char need_mb;
	/* Data used for registry */
	struct list_head head __attribute__((aligned(CACHE_LINE_SIZE)));
	pthread_t tid;
};

extern struct urcu_reader __thread urcu_reader;

extern int gp_futex;

/*
 * Wake-up waiting synchronize_rcu(). Called from many concurrent threads.
 */
static inline void wake_up_gp(void)
{
	if (unlikely(uatomic_read(&gp_futex) == -1)) {
		uatomic_set(&gp_futex, 0);
		futex_async(&gp_futex, FUTEX_WAKE, 1,
		      NULL, NULL, 0);
	}
}

static inline int rcu_old_gp_ongoing(long *value)
{
	long v;

	if (value == NULL)
		return 0;
	/*
	 * Make sure both tests below are done on the same version of *value
	 * to insure consistency.
	 */
	v = LOAD_SHARED(*value);
	return (v & RCU_GP_CTR_NEST_MASK) &&
		 ((v ^ urcu_gp_ctr) & RCU_GP_CTR_BIT);
}

static inline void _rcu_read_lock(void)
{
	long tmp;

	tmp = urcu_reader.ctr;
	/* urcu_gp_ctr = RCU_GP_COUNT | (~RCU_GP_CTR_BIT or RCU_GP_CTR_BIT) */
	if (likely(!(tmp & RCU_GP_CTR_NEST_MASK))) {
		_STORE_SHARED(urcu_reader.ctr, _LOAD_SHARED(urcu_gp_ctr));
		/*
		 * Set active readers count for outermost nesting level before
		 * accessing the pointer. See force_mb_all_threads().
		 */
		reader_barrier();
	} else {
		_STORE_SHARED(urcu_reader.ctr, tmp + RCU_GP_COUNT);
	}
}

static inline void _rcu_read_unlock(void)
{
	long tmp;

	tmp = urcu_reader.ctr;
	/*
	 * Finish using rcu before decrementing the pointer.
	 * See force_mb_all_threads().
	 */
	if (likely((tmp & RCU_GP_CTR_NEST_MASK) == RCU_GP_COUNT)) {
		reader_barrier();
		_STORE_SHARED(urcu_reader.ctr, urcu_reader.ctr - RCU_GP_COUNT);
		/* write urcu_reader.ctr before read futex */
		reader_barrier();
		wake_up_gp();
	} else {
		_STORE_SHARED(urcu_reader.ctr, urcu_reader.ctr - RCU_GP_COUNT);
	}
}

#ifdef __cplusplus 
}
#endif

#endif /* _URCU_STATIC_H */
