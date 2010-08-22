/*
 * rculfstack.c
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

/* Use the urcu symbols to select the appropriate rcu flavor at link time */
#include "urcu.h"
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include "urcu/rculfstack.h"
#include "urcu/rculfstack-static.h"

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */


void rcu_lfs_node_init(struct rcu_lfs_node *node)
{
	_rcu_lfs_node_init(node);
}

void rcu_lfs_init(struct rcu_lfs_stack *s)
{
	_rcu_lfs_init(s);
}

void rcu_lfs_push(struct rcu_lfs_stack *s, struct rcu_lfs_node *node)
{
	_rcu_lfs_push(s, node);
}

struct rcu_lfs_node *rcu_lfs_pop(struct rcu_lfs_stack *s)
{
	return _rcu_lfs_pop(s);
}
