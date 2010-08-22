/*
 * rculfqueue.c
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

/* Use the urcu symbols to select the appropriate rcu flavor at link time */
#include "urcu.h"
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include "urcu/rculfqueue.h"
#include "urcu/rculfqueue-static.h"

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

void rcu_lfq_node_init(struct rcu_lfq_node *node)
{
	_rcu_lfq_node_init(node);
}

void rcu_lfq_init(struct rcu_lfq_queue *q)
{
	_rcu_lfq_init(q);
}

void rcu_lfq_enqueue(struct rcu_lfq_queue *q, struct rcu_lfq_node *node)
{
	_rcu_lfq_enqueue(q, node);
}

struct rcu_lfq_node *
rcu_lfq_dequeue(struct rcu_lfq_queue *q, void (*release)(struct urcu_ref *))
{
	return _rcu_lfq_dequeue(q, release);
}
