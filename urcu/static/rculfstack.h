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

#include <urcu/uatomic.h>
/* A urcu implementation header should be already included. */

#ifdef __cplusplus
extern "C" {
#endif

void _cds_lfs_node_init_rcu(struct cds_lfs_node_rcu *node)
{
}

void _cds_lfs_init_rcu(struct cds_lfs_stack_rcu *s)
{
	s->head = NULL;
}

void _cds_lfs_push_rcu(struct cds_lfs_stack_rcu *s, struct cds_lfs_node_rcu *node)
{
	struct cds_lfs_node_rcu *head = NULL;

	for (;;) {
		struct cds_lfs_node_rcu *old_head = head;

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
 * Should be called under rcu read-side lock.
 *
 * The caller must wait for a grace period to pass before freeing the returned
 * node or modifying the cds_lfs_node_rcu structure.
 * Returns NULL if stack is empty.
 */
struct cds_lfs_node_rcu *
_cds_lfs_pop_rcu(struct cds_lfs_stack_rcu *s)
{
	for (;;) {
		struct cds_lfs_node_rcu *head;

		head = rcu_dereference(s->head);
		if (head) {
			struct cds_lfs_node_rcu *next = rcu_dereference(head->next);

			if (uatomic_cmpxchg(&s->head, head, next) == head) {
				return head;
			} else {
				/* Concurrent modification. Retry. */
				continue;
			}
		} else {
			/* Empty stack */
			return NULL;
		}
	}
}

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFSTACK_STATIC_H */
