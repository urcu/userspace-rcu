#ifndef _URCU_RECLAIM_STATIC_H
#define _URCU_RECLAIM_STATIC_H

/*
 * urcu-reclaim-static.h
 *
 * Userspace RCU header - memory reclamation.
 *
 * TO BE INCLUDED ONLY IN LGPL-COMPATIBLE CODE. See urcu-reclaim.h for linking
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

#include <compiler.h>
#include <arch.h>


/*
 * Number of entries in the per-thread reclaim queue. Must be power of 2.
 */
#define RECLAIM_QUEUE_SIZE	(1 << 12)
#define RECLAIM_QUEUE_MASK	(RECLAIM_QUEUE_SIZE - 1)

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

struct reclaim_queue {
	unsigned long head;	/* add element at head */
	unsigned long tail;	/* next element to remove at tail */
	void **q;
};

extern struct reclaim_queue __thread reclaim_queue;

extern void rcu_reclaim_barrier_thread(void);

/*
 * not signal-safe.
 */
static inline void _rcu_reclaim_queue(void *p)
{
	unsigned long head, tail;

	/*
	 * Head is only modified by ourself. Tail can be modified by reclamation
	 * thread.
	 */
	head = reclaim_queue.head;
	tail = LOAD_SHARED(reclaim_queue.tail);

	/*
	 * If queue is full, empty it ourself.
	 */
	if (unlikely(head - tail >= RECLAIM_QUEUE_SIZE)) {
		assert(head - tail == RECLAIM_QUEUE_SIZE);
		rcu_reclaim_barrier_thread();
		assert(head - LOAD_SHARED(reclaim_queue.tail) == 0);
	}

	smp_wmb();	/* Publish new pointer before write q[] */
	_STORE_SHARED(reclaim_queue.q[head & RECLAIM_QUEUE_MASK], p);
	smp_wmb();	/* Write q[] before head. */
	STORE_SHARED(reclaim_queue.head, head + 1);
}

#endif /* _URCU_RECLAIM_STATIC_H */
