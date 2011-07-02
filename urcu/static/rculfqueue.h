#ifndef _URCU_RCULFQUEUE_STATIC_H
#define _URCU_RCULFQUEUE_STATIC_H

/*
 * rculfqueue-static.h
 *
 * Userspace RCU library - Lock-Free RCU Queue
 *
 * Copyright 2010 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 *
 * TO BE INCLUDED ONLY IN LGPL-COMPATIBLE CODE. See rculfqueue.h for linking
 * dynamically with the userspace rcu library.
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

#include <urcu/ref.h>
#include <urcu/uatomic.h>
#include <assert.h>
/* A urcu implementation header should be already included. */

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

#define URCU_LFQ_PERMANENT_REF		128

void _cds_lfq_node_init_rcu(struct cds_lfq_node_rcu *node)
{
	node->next = NULL;
	urcu_ref_init(&node->ref);
}

void _cds_lfq_init_rcu(struct cds_lfq_queue_rcu *q,
		       void (*release)(struct urcu_ref *ref))
{
	_cds_lfq_node_init_rcu(&q->init);
	/* Make sure the initial node is never freed. */
	urcu_ref_set(&q->init.ref, URCU_LFQ_PERMANENT_REF);
	q->head = q->tail = &q->init;
	q->release = release;
}

/*
 * Should be called under rcu read lock critical section.
 */
void _cds_lfq_enqueue_rcu(struct cds_lfq_queue_rcu *q,
			  struct cds_lfq_node_rcu *node)
{
	urcu_ref_get(&node->ref);
	node->queue = q;

	/*
	 * uatomic_cmpxchg() implicit memory barrier orders earlier stores to
	 * node before publication.
	 */

	for (;;) {
		struct cds_lfq_node_rcu *tail, *next;

		tail = rcu_dereference(q->tail);
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
			(void) uatomic_cmpxchg(&q->tail, tail, node);
			return;
		} else {
			/*
			 * Failure to append to current tail. Help moving tail
			 * further and retry.
			 */
			(void) uatomic_cmpxchg(&q->tail, tail, next);
			continue;
		}
	}
}

/*
 * Should be called under rcu read lock critical section.
 *
 * The entry returned by dequeue must be taken care of by doing a
 * sequence of urcu_ref_put which release handler should do a call_rcu.
 *
 * In other words, the entry lfq node returned by dequeue must not be
 * modified/re-used/freed until the reference count reaches zero and a grace
 * period has elapsed.
 */
struct cds_lfq_node_rcu *_cds_lfq_dequeue_rcu(struct cds_lfq_queue_rcu *q)
{
	for (;;) {
		struct cds_lfq_node_rcu *head, *next;

		head = rcu_dereference(q->head);
		next = rcu_dereference(head->next);
		if (next) {
			if (uatomic_cmpxchg(&q->head, head, next) == head) {
				urcu_ref_put(&head->ref, q->release);
				return next;
			} else {
				/* Concurrently pushed, retry */
				continue;
			}
		} else {
			/* Empty */
			return NULL;
		}
	}
}

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFQUEUE_STATIC_H */
