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
#include <assert.h>
#include <limits.h>

#include <compiler.h>
#include <arch.h>

/*
 * Identify a shared load. A smp_rmc() or smp_mc() should come before the load.
 */
#define _LOAD_SHARED(p)	       ACCESS_ONCE(p)

/*
 * Load a data from shared memory, doing a cache flush if required.
 */
#define LOAD_SHARED(p)			\
	({				\
		smp_rmc();		\
		_LOAD_SHARED(p);	\
	})

/*
 * Identify a shared store. A smp_wmc() or smp_mc() should follow the store.
 */
#define _STORE_SHARED(x, v)	({ ACCESS_ONCE(x) = (v); })

/*
 * Store v into x, where x is located in shared memory. Performs the required
 * cache flush after writing. Returns v.
 */
#define STORE_SHARED(x, v)		\
	({				\
		_STORE_SHARED(x, v);	\
		smp_wmc();		\
		(v);			\
	})

/**
 * _rcu_dereference - reads (copy) a RCU-protected pointer to a local variable
 * into a RCU read-side critical section. The pointer can later be safely
 * dereferenced within the critical section.
 *
 * This ensures that the pointer copy is invariant thorough the whole critical
 * section.
 *
 * Inserts memory barriers on architectures that require them (currently only
 * Alpha) and documents which pointers are protected by RCU.
 *
 * Should match rcu_assign_pointer() or rcu_xchg_pointer().
 */

#define _rcu_dereference(p)     ({					\
				typeof(p) _________p1 = LOAD_SHARED(p); \
				smp_read_barrier_depends();		\
				(_________p1);				\
				})

/*
 * This code section can only be included in LGPL 2.1 compatible source code.
 * See below for the function call wrappers which can be used in code meant to
 * be only linked with the Userspace RCU library. This comes with a small
 * performance degradation on the read-side due to the added function calls.
 * This is required to permit relinking with newer versions of the library.
 */

/*
 * If a reader is really non-cooperative and refuses to commit its
 * rcu_reader_qs_gp count to memory (there is no barrier in the reader
 * per-se), kick it after a few loops waiting for it.
 */
#define KICK_READER_LOOPS 10000

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

static inline void reader_barrier()
{
	smp_mb();
}

#define RCU_GP_ONLINE		(1UL << 0)
#define RCU_GP_CTR		(1UL << 1)

/*
 * Global quiescent period counter with low-order bits unused.
 * Using a int rather than a char to eliminate false register dependencies
 * causing stalls on some architectures.
 */
extern unsigned long urcu_gp_ctr;

extern unsigned long __thread rcu_reader_qs_gp;

static inline int rcu_gp_ongoing(unsigned long *value)
{
	unsigned long reader_gp;

	if (value == NULL)
		return 0;
	reader_gp = LOAD_SHARED(*value);
	return reader_gp && (reader_gp - urcu_gp_ctr > ULONG_MAX / 2);
}

static inline void _rcu_read_lock(void)
{
	rcu_assert(rcu_reader_qs_gp);
}

static inline void _rcu_read_unlock(void)
{
}

static inline void _rcu_quiescent_state(void)
{
	smp_mb();	
	_STORE_SHARED(rcu_reader_qs_gp, _LOAD_SHARED(urcu_gp_ctr));
	smp_mb();
}

static inline void _rcu_thread_offline(void)
{
	smp_mb();
	STORE_SHARED(rcu_reader_qs_gp, 0);
}

static inline void _rcu_thread_online(void)
{
	_STORE_SHARED(rcu_reader_qs_gp, LOAD_SHARED(urcu_gp_ctr));
	smp_mb();
}

/**
 * _rcu_assign_pointer - assign (publicize) a pointer to a new data structure
 * meant to be read by RCU read-side critical sections. Returns the assigned
 * value.
 *
 * Documents which pointers will be dereferenced by RCU read-side critical
 * sections and adds the required memory barriers on architectures requiring
 * them. It also makes sure the compiler does not reorder code initializing the
 * data structure before its publication.
 *
 * Should match rcu_dereference_pointer().
 */

#define _rcu_assign_pointer(p, v)			\
	({						\
		if (!__builtin_constant_p(v) || 	\
		    ((v) != NULL))			\
			wmb();				\
		STORE_SHARED(p, v);			\
	})

/**
 * _rcu_xchg_pointer - same as rcu_assign_pointer, but returns the previous
 * pointer to the data structure, which can be safely freed after waiting for a
 * quiescent state using synchronize_rcu().
 */

#define _rcu_xchg_pointer(p, v)				\
	({						\
		if (!__builtin_constant_p(v) ||		\
		    ((v) != NULL))			\
			wmb();				\
		xchg(p, v);				\
	})

/*
 * Exchanges the pointer and waits for quiescent state.
 * The pointer returned can be freed.
 */
#define _rcu_publish_content(p, v)			\
	({						\
		void *oldptr;				\
		oldptr = _rcu_xchg_pointer(p, v);	\
		synchronize_rcu();			\
		oldptr;					\
	})

#endif /* _URCU_QSBR_STATIC_H */
