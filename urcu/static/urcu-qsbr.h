#ifndef _URCU_QSBR_STATIC_H
#define _URCU_QSBR_STATIC_H

/*
 * urcu-qsbr-static.h
 *
 * Userspace RCU QSBR header.
 *
 * TO BE INCLUDED ONLY IN LGPL-COMPATIBLE CODE. See urcu-qsbr.h for linking
 * dynamically with the userspace rcu QSBR library.
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
#include <assert.h>
#include <limits.h>
#include <unistd.h>
#include <stdint.h>

#include <urcu/compiler.h>
#include <urcu/arch.h>
#include <urcu/system.h>
#include <urcu/uatomic.h>
#include <urcu/list.h>
#include <urcu/futex.h>

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

/* maximum sleep delay, in us */
#define MAX_SLEEP 50

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

#define RCU_GP_ONLINE		(1UL << 0)
#define RCU_GP_CTR		(1UL << 1)

/*
 * Global quiescent period counter with low-order bits unused.
 * Using a int rather than a char to eliminate false register dependencies
 * causing stalls on some architectures.
 */
extern unsigned long rcu_gp_ctr;

struct rcu_reader {
	/* Data used by both reader and synchronize_rcu() */
	unsigned long ctr;
	/* Data used for registry */
	struct cds_list_head node __attribute__((aligned(CAA_CACHE_LINE_SIZE)));
	int waiting;
	pthread_t tid;
};

extern struct rcu_reader __thread rcu_reader;

extern int32_t gp_futex;

/*
 * Wake-up waiting synchronize_rcu(). Called from many concurrent threads.
 */
static inline void wake_up_gp(void)
{
	if (caa_unlikely(_CMM_LOAD_SHARED(rcu_reader.waiting))) {
		_CMM_STORE_SHARED(rcu_reader.waiting, 0);
		cmm_smp_mb();
		if (uatomic_read(&gp_futex) != -1)
			return;
		uatomic_set(&gp_futex, 0);
		futex_noasync(&gp_futex, FUTEX_WAKE, 1,
		      NULL, NULL, 0);
	}
}

static inline int rcu_gp_ongoing(unsigned long *ctr)
{
	unsigned long v;

	v = CMM_LOAD_SHARED(*ctr);
	return v && (v != rcu_gp_ctr);
}

static inline void _rcu_read_lock(void)
{
	rcu_assert(rcu_reader.ctr);
}

static inline void _rcu_read_unlock(void)
{
}

static inline void _rcu_quiescent_state(void)
{
	cmm_smp_mb();
	_CMM_STORE_SHARED(rcu_reader.ctr, _CMM_LOAD_SHARED(rcu_gp_ctr));
	cmm_smp_mb();	/* write rcu_reader.ctr before read futex */
	wake_up_gp();
	cmm_smp_mb();
}

static inline void _rcu_thread_offline(void)
{
	cmm_smp_mb();
	CMM_STORE_SHARED(rcu_reader.ctr, 0);
	cmm_smp_mb();	/* write rcu_reader.ctr before read futex */
	wake_up_gp();
	cmm_barrier();	/* Ensure the compiler does not reorder us with mutex */
}

static inline void _rcu_thread_online(void)
{
	cmm_barrier();	/* Ensure the compiler does not reorder us with mutex */
	_CMM_STORE_SHARED(rcu_reader.ctr, CMM_LOAD_SHARED(rcu_gp_ctr));
	cmm_smp_mb();
}

#ifdef __cplusplus 
}
#endif

#endif /* _URCU_QSBR_STATIC_H */
