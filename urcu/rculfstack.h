#ifndef _URCU_RCULFSTACK_H
#define _URCU_RCULFSTACK_H

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

#ifdef __cplusplus
extern "C" {
#endif

struct rcu_lfs_node {
	struct rcu_lfs_node *next;
};

struct rcu_lfs_stack {
	struct rcu_lfs_node *head;
};

#ifdef _LGPL_SOURCE

#include <urcu/rculfstack-static.h>

#define rcu_lfs_node_init	_rcu_lfs_node_init
#define rcu_lfs_init		_rcu_lfs_init
#define rcu_lfs_push		_rcu_lfs_push
#define rcu_lfs_pop		_rcu_lfs_pop

#else /* !_LGPL_SOURCE */

extern void rcu_lfs_node_init(struct rcu_lfs_node *node);
extern void rcu_lfs_init(struct rcu_lfs_stack *s);
extern void rcu_lfs_push(struct rcu_lfs_stack *s, struct rcu_lfs_node *node);

/*
 * The caller must wait for a grace period to pass before freeing the returned
 * node or modifying the rcu_lfs_node structure.
 * Returns NULL if stack is empty.
 */
extern struct rcu_lfs_node *rcu_lfs_pop(struct rcu_lfs_stack *s);

#endif /* !_LGPL_SOURCE */

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFSTACK_H */
