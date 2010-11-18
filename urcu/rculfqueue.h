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

struct cds_lfq_node_rcu {
	struct cds_lfq_node_rcu *next;
	struct urcu_ref ref;
};

struct cds_lfq_queue_rcu {
	struct cds_lfq_node_rcu *head, *tail;
	struct cds_lfq_node_rcu init;	/* Dummy initialization node */
};

#ifdef _LGPL_SOURCE

#include <urcu/rculfqueue-static.h>

#define cds_lfq_node_init_rcu	_cds_lfq_node_init_rcu
#define cds_lfq_init_rcu		_cds_lfq_init_rcu
#define cds_lfq_enqueue_rcu		_cds_lfq_enqueue_rcu
#define cds_lfq_dequeue_rcu		_cds_lfq_dequeue_rcu

#else /* !_LGPL_SOURCE */

extern void cds_lfq_node_init_rcu(struct cds_lfq_node_rcu *node);
extern void cds_lfq_init_rcu(struct cds_lfq_queue_rcu *q);
extern void cds_lfq_enqueue_rcu(struct cds_lfq_queue_rcu *q, struct cds_lfq_node_rcu *node);

/*
 * The entry returned by dequeue must be taken care of by doing a urcu_ref_put,
 * which calls the release primitive when the reference count drops to zero. A
 * grace period must be waited after execution of the release callback before
 * performing the actual memory reclamation or modifying the cds_lfq_node_rcu
 * structure.
 * In other words, the entry lfq node returned by dequeue must not be
 * modified/re-used/freed until the reference count reaches zero and a grace
 * period has elapsed (after the refcount reached 0).
 */
extern struct cds_lfq_node_rcu *
cds_lfq_dequeue_rcu(struct cds_lfq_queue_rcu *q, void (*release)(struct urcu_ref *));

#endif /* !_LGPL_SOURCE */

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFQUEUE_H */
