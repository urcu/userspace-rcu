#ifndef _URCU_DEFER_STATIC_H
#define _URCU_DEFER_STATIC_H

/*
 * urcu-defer-static.h
 *
 * Userspace RCU header - memory reclamation.
 *
 * TO BE INCLUDED ONLY IN LGPL-COMPATIBLE CODE. See urcu-defer.h for linking
 * dynamically with the userspace rcu reclamation library.
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

#include <urcu/compiler.h>
#include <urcu/arch.h>
#include <urcu/uatomic_arch.h>
#include <urcu/list.h>


/*
 * Number of entries in the per-thread defer queue. Must be power of 2.
 */
#define DEFER_QUEUE_SIZE	(1 << 12)
#define DEFER_QUEUE_MASK	(DEFER_QUEUE_SIZE - 1)

/*
 * Typically, data is aligned at least on the architecture size.
 * Use lowest bit to indicate that the current callback is changing.
 * Assumes that (void *)-2L is not used often. Used to encode non-aligned
 * functions and non-aligned data using extra space.
 * We encode the (void *)-2L fct as: -2L, fct, data.
 * We encode the (void *)-2L data as: -2L, fct, data.
 * Here, DQ_FCT_MARK == ~DQ_FCT_BIT. Required for the test order.
 */
#define DQ_FCT_BIT		(1 << 0)
#define DQ_IS_FCT_BIT(x)	((unsigned long)(x) & DQ_FCT_BIT)
#define DQ_SET_FCT_BIT(x)	\
	(x = (void *)((unsigned long)(x) | DQ_FCT_BIT))
#define DQ_CLEAR_FCT_BIT(x)	\
	(x = (void *)((unsigned long)(x) & ~DQ_FCT_BIT))
#define DQ_FCT_MARK		((void *)(~DQ_FCT_BIT))

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

/*
 * defer queue.
 * Contains pointers. Encoded to save space when same callback is often used.
 * When looking up the next item:
 * - if DQ_FCT_BIT is set, set the current callback to DQ_CLEAR_FCT_BIT(ptr)
 *   - next element contains pointer to data.
 * - else if item == DQ_FCT_MARK
 *   - set the current callback to next element ptr
 *   - following next element contains pointer to data.
 * - else current element contains data
 */
struct defer_queue {
	unsigned long head;	/* add element at head */
	void *last_fct_in;	/* last fct pointer encoded */
	unsigned long tail;	/* next element to remove at tail */
	void *last_fct_out;	/* last fct pointer encoded */
	void **q;
	/* registry information */
	unsigned long last_head;
	struct list_head list;	/* list of thread queues */
};

#endif /* _URCU_DEFER_STATIC_H */
