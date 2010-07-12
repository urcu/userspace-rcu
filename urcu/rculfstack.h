/*
 * rculfstack.h
 *
 * Userspace RCU library - Lock-Free RCU Stack
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

#if (!defined(_GNU_SOURCE) && !defined(_LGPL_SOURCE))
#error "Dynamic loader LGPL wrappers not implemented yet"
#endif

struct rcu_lfs_node {
	struct rcu_lfs_node *next;
};

struct rcu_lfs_stack {
	struct rcu_lfs_node *head;
};

void rcu_lfs_node_init(struct rcu_lfs_node *node)
{
}

void rcu_lfs_init(struct rcu_lfs_stack *s)
{
	s->head = NULL;
}

void rcu_lfs_push(struct rcu_lfs_stack *s, struct rcu_lfs_node *node)
{
	rcu_read_lock();
	for (;;) {
		struct rcu_lfs_node *head = rcu_dereference(s->head);

		node->next = head;
		/*
		 * uatomic_cmpxchg() implicit memory barrier orders earlier
		 * stores to node before publication.
		 */
		if (uatomic_cmpxchg(&s->head, head, node) == head) {
			rcu_read_unlock();
			return;
		} else {
			/* Failure to prepend. Retry. */
			continue;
		}
	}
}

/*
 * The caller must wait for a grace period to pass before freeing the returned
 * node.
 * Returns NULL if stack is empty.
 */
struct rcu_lfs_node *
rcu_lfs_pop(struct rcu_lfs_stack *s)
{
	rcu_read_lock();
	for (;;) {
		struct rcu_lfs_node *head = rcu_dereference(s->head);

		if (head) {
			struct rcu_lfs_node *next = rcu_dereference(head->next);

			if (uatomic_cmpxchg(&s->head, head, next) == head) {
				rcu_read_unlock();
				return head;
			} else {
				/* Concurrent modification. Retry. */
				continue;
			}
		} else {
			/* Empty stack */
			rcu_read_unlock();
			return NULL;
		}
	}
}
