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

#if (!defined(_GNU_SOURCE) && !defined(_LGPL_SOURCE))
#error "Dynamic loader LGPL wrappers not implemented yet"
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

#define URCU_LFQ_PERMANENT_REF		128

struct rcu_lfq_node {
	struct rcu_lfq_node *next;
	struct urcu_ref ref;
};

struct rcu_lfq_queue {
	struct rcu_lfq_node *head, *tail;
	struct rcu_lfq_node init;	/* Dummy initialization node */
};

void rcu_lfq_node_init(struct rcu_lfq_node *node)
{
	node->next = NULL;
	urcu_ref_init(&node->ref);
}

void rcu_lfq_init(struct rcu_lfq_queue *q)
{
	rcu_lfq_node_init(&q->init);
	/* Make sure the initial node is never freed. */
	urcu_ref_set(&q->init.ref, URCU_LFQ_PERMANENT_REF);
	q->head = q->tail = &q->init;
}

void rcu_lfq_enqueue(struct rcu_lfq_queue *q, struct rcu_lfq_node *node)
{
	urcu_ref_get(&node->ref);

	/*
	 * uatomic_cmpxchg() implicit memory barrier orders earlier stores to
	 * node before publication.
	 */

	rcu_read_lock();
	for (;;) {
		struct rcu_lfq_node *tail = rcu_dereference(q->tail);
		struct rcu_lfq_node *next;

		/*
		 * Typically expect tail->next to be NULL.
		 */
		next = uatomic_cmpxchg(&tail->next, NULL, node);
		if (next == NULL) {
			/*
			 * Tail was at the end of queue, we successfully
			 * appended to it.
			 * Now move tail (another enqueue might beat
			 * us to it, that's fine).
			 */
			uatomic_cmpxchg(&q->tail, tail, node);
			rcu_read_unlock();
			return;
		} else {
			/*
			 * Failure to append to current tail. Help moving tail
			 * further and retry.
			 */
			uatomic_cmpxchg(&q->tail, tail, next);
			continue;
		}
	}
}

/*
 * The entry returned by dequeue must be taken care of by doing a urcu_ref_put,
 * which calls the release primitive when the reference count drops to zero. A
 * grace period must be waited before performing the actual memory reclamation
 * in the release primitive.
 * The entry lfq node returned by dequeue must no be re-used before the
 * reference count reaches zero.
 */
struct rcu_lfq_node *
rcu_lfq_dequeue(struct rcu_lfq_queue *q, void (*release)(struct urcu_ref *))
{
	rcu_read_lock();
	for (;;) {
		struct rcu_lfq_node *head = rcu_dereference(q->head);
		struct rcu_lfq_node *next = rcu_dereference(head->next);

		if (next) {
			if (uatomic_cmpxchg(&q->head, head, next) == head) {
				rcu_read_unlock();
				urcu_ref_put(&head->ref, release);
				return next;
			} else {
				/* Concurrently pushed, retry */
				continue;
			}
		} else {
			/* Empty */
			rcu_read_unlock();
			return NULL;
		}
	}
}
