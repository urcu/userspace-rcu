/*
 * rcuwfqueue.h
 *
 * Userspace RCU library - RCU Queue with Wait-Free Enqueue/Blocking Dequeue
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
 * RCU queue with wait-free enqueue/blocking dequeue using reference counting.
 * Enqueue and dequeue operations hold a RCU read lock to deal with cmpxchg ABA
 * problem. This implementation keeps a dummy head node to ensure we can always
 * update the queue locklessly. Given that this is a queue, the dummy head node
 * must always advance as we dequeue entries. Therefore, we keep a reference
 * count on each entry we are dequeueing, so they can be kept as dummy head node
 * until the next dequeue, at which point their reference count will be
 * decremented.
 */

#define URCU_WFQ_PERMANENT_REF		128

struct rcu_wfq_node {
	struct rcu_wfq_node *next;
	struct urcu_ref ref;
};

struct rcu_wfq_queue {
	struct rcu_wfq_node *head, *tail;
	struct rcu_wfq_node init;	/* Dummy initialization node */
};

void rcu_wfq_node_init(struct rcu_wfq_node *node)
{
	node->next = NULL;
	urcu_ref_init(&node->ref);
}

void rcu_wfq_init(struct rcu_wfq_queue *q)
{
	rcu_wfq_node_init(&q->init);
	/* Make sure the initial node is never freed. */
	urcu_ref_set(&q->init.ref, URCU_WFQ_PERMANENT_REF);
	/* Set queue end */
	q->head = q->tail = &q->init;
}

void rcu_wfq_enqueue(struct rcu_wfq_queue *q, struct rcu_wfq_node *node)
{
	struct rcu_wfq_node *old_tail;

	urcu_ref_get(&node->ref);
	/*
	 * uatomic_xchg() implicit memory barrier orders earlier stores to node
	 * (setting it to NULL and incrementing the refcount) before
	 * publication.
	 */
	old_tail = uatomic_xchg(&q->tail, node);
	/*
	 * At this point, dequeuers see a NULL old_tail->next, which indicates
	 * end of queue. The following store will append "node" to the queue
	 * from a dequeuer perspective.
	 */
	STORE_SHARED(old_tail->next, node);
}

/*
 * The entry returned by dequeue must be taken care of by doing a urcu_ref_put,
 * which calls the release primitive when the reference count drops to zero. A
 * grace period must be waited before performing the actual memory reclamation
 * in the release primitive. The wfq node returned by dequeue must not be
 * modified/re-used/freed until the reference count reaches zero and a grace
 * period has elapsed (after the refcount reached 0).
 *
 * TODO: implement adaptative busy-wait and wait/wakeup scheme rather than busy
 * loops. Better for UP.
 */
struct rcu_wfq_node *
rcu_wfq_dequeue_blocking(struct rcu_wfq_queue *q,
			 void (*release)(struct urcu_ref *))
{
	for (;;) {
		struct rcu_wfq_node *head, *next;

		rcu_read_lock();
		head = rcu_dereference(q->head);
		next = rcu_dereference(head->next);
		if (next) {
			if (uatomic_cmpxchg(&q->head, head, next) == head) {
				rcu_read_unlock();
				urcu_ref_put(&head->ref, release);
				return next;
			} else {
				/* Concurrently pushed, retry */
				rcu_read_unlock();
				continue;
			}
		} else {
			/* Empty */
			rcu_read_unlock();
			return NULL;
		}
	}
}
