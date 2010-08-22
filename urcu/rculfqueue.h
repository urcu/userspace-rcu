#ifndef _URCU_RCULFQUEUE_H
#define _URCU_RCULFQUEUE_H

/*
 * rculfqueue.h
 *
 * Userspace RCU library - Lock-Free RCU Queue
 *
 * Copyright 2010 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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
 */

#include <urcu/urcu_ref.h>
#include <assert.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Lock-free RCU queue using reference counting. Enqueue and dequeue operations
 * hold a RCU read lock to deal with cmpxchg ABA problem. This implementation
 * keeps a dummy head node to ensure we can always update the queue locklessly.
 * Given that this is a queue, the dummy head node must always advance as we
 * dequeue entries. Therefore, we keep a reference count on each entry we are
 * dequeueing, so they can be kept as dummy head node until the next dequeue, at
 * which point their reference count will be decremented.
 */

struct rcu_lfq_node {
	struct rcu_lfq_node *next;
	struct urcu_ref ref;
};

struct rcu_lfq_queue {
	struct rcu_lfq_node *head, *tail;
	struct rcu_lfq_node init;	/* Dummy initialization node */
};

#ifdef _LGPL_SOURCE

#include <urcu/rculfqueue-static.h>

#define rcu_lfq_node_init	_rcu_lfq_node_init
#define rcu_lfq_init		_rcu_lfq_init
#define rcu_lfq_enqueue		_rcu_lfq_enqueue
#define rcu_lfq_dequeue		_rcu_lfq_dequeue

#else /* !_LGPL_SOURCE */

extern void rcu_lfq_node_init(struct rcu_lfq_node *node);
extern void rcu_lfq_init(struct rcu_lfq_queue *q);
extern void rcu_lfq_enqueue(struct rcu_lfq_queue *q, struct rcu_lfq_node *node);

/*
 * The entry returned by dequeue must be taken care of by doing a urcu_ref_put,
 * which calls the release primitive when the reference count drops to zero. A
 * grace period must be waited after execution of the release callback before
 * performing the actual memory reclamation or modifying the rcu_lfq_node
 * structure.
 * In other words, the entry lfq node returned by dequeue must not be
 * modified/re-used/freed until the reference count reaches zero and a grace
 * period has elapsed (after the refcount reached 0).
 */
extern struct rcu_lfq_node *
rcu_lfq_dequeue(struct rcu_lfq_queue *q, void (*release)(struct urcu_ref *));

#endif /* !_LGPL_SOURCE */

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFQUEUE_H */
