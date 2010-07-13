#ifndef _URCU_RCUWFSTACK_H
#define _URCU_RCUWFSTACK_H

/*
 * rcuwfstack.h
 *
 * Userspace RCU library - RCU Stack with Wait-Free push, Blocking pop.
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

#include <assert.h>

#if (!defined(_GNU_SOURCE) && !defined(_LGPL_SOURCE))
#error "Dynamic loader LGPL wrappers not implemented yet"
#endif

#define RCU_WF_STACK_END		((void *)0x1UL)

struct rcu_wfs_node {
	struct rcu_wfs_node *next;
};

struct rcu_wfs_stack {
	struct rcu_wfs_node *head;
};

void rcu_wfs_node_init(struct rcu_wfs_node *node)
{
	node->next = NULL;
}

void rcu_wfs_init(struct rcu_wfs_stack *s)
{
	s->head = RCU_WF_STACK_END;
}

void rcu_wfs_push(struct rcu_wfs_stack *s, struct rcu_wfs_node *node)
{
	struct rcu_wfs_node *old_head;

	assert(node->next == NULL);
	/*
	 * uatomic_xchg() implicit memory barrier orders earlier stores to node
	 * (setting it to NULL) before publication.
	 */
	old_head = uatomic_xchg(&s->head, node);
	/*
	 * At this point, dequeuers see a NULL node->next, they should busy-wait
	 * until node->next is set to old_head.
	 */
	STORE_SHARED(node->next, old_head);
}

/*
 * The caller must wait for a grace period before:
 * - freeing the returned node.
 * - modifying the ->next pointer of the returned node. (be careful with unions)
 * - passing the returned node back to push() on the same stack they got it
 *   from.
 *
 * Returns NULL if stack is empty.
 *
 * cmpxchg is protected from ABA races by holding a RCU read lock between
 * s->head read and cmpxchg modifying s->head and requiring that dequeuers wait
 * for a grace period before freeing the returned node.
 *
 * TODO: implement adaptative busy-wait and wait/wakeup scheme rather than busy
 * loops. Better for UP.
 */
struct rcu_wfs_node *
rcu_wfs_pop_blocking(struct rcu_wfs_stack *s)
{
	for (;;) {
		struct rcu_wfs_node *head;

		rcu_read_lock();
		head = rcu_dereference(s->head);
		if (head != RCU_WF_STACK_END) {
			struct rcu_wfs_node *next = rcu_dereference(head->next);

			/* Retry while head is being set by push(). */
			if (!next) {
				rcu_read_unlock();
				continue;
			}
			if (uatomic_cmpxchg(&s->head, head, next) == head) {
				rcu_read_unlock();
				return head;
			} else {
				/* Concurrent modification. Retry. */
				rcu_read_unlock();
				continue;
			}
		} else {
			/* Empty stack */
			rcu_read_unlock();
			return NULL;
		}
	}
}

#endif /* _URCU_RCUWFSTACK_H */
