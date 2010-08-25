#ifndef _URCU_RCULFSTACK_STATIC_H
#define _URCU_RCULFSTACK_STATIC_H

/*
 * rculfstack-static.h
 *
 * Userspace RCU library - Lock-Free RCU Stack
 *
 * Copyright 2010 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 *
 * TO BE INCLUDED ONLY IN LGPL-COMPATIBLE CODE. See rculfstack.h for linking
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

#include <urcu/uatomic_arch.h>
/* A urcu implementation header should be already included. */

#ifdef __cplusplus
extern "C" {
#endif

void _rcu_lfs_node_init(struct rcu_lfs_node *node)
{
}

void _rcu_lfs_init(struct rcu_lfs_stack *s)
{
	s->head = NULL;
}

void _rcu_lfs_push(struct rcu_lfs_stack *s, struct rcu_lfs_node *node)
{
	struct rcu_lfs_node *head = NULL;

	for (;;) {
		struct rcu_lfs_node *old_head = head;

		node->next = head;
		/*
		 * uatomic_cmpxchg() implicit memory barrier orders earlier
		 * stores to node before publication.
		 */
		head = uatomic_cmpxchg(&s->head, old_head, node);
		if (old_head == head)
			break;
	}
}

/*
 * The caller must wait for a grace period to pass before freeing the returned
 * node or modifying the rcu_lfs_node structure.
 * Returns NULL if stack is empty.
 */
struct rcu_lfs_node *
_rcu_lfs_pop(struct rcu_lfs_stack *s)
{
	for (;;) {
		struct rcu_lfs_node *head;

		rcu_read_lock();
		head = rcu_dereference(s->head);
		if (head) {
			struct rcu_lfs_node *next = rcu_dereference(head->next);

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

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFSTACK_STATIC_H */
