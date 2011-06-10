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

#define _LGPL_SOURCE
/* Use the urcu symbols to select the appropriate rcu flavor at link time */
#include "urcu.h"

#undef _LGPL_SOURCE
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include "urcu/rculfqueue.h"
#include "urcu/static/rculfqueue.h"

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

void cds_lfq_node_init_rcu(struct cds_lfq_node_rcu *node)
{
	_cds_lfq_node_init_rcu(node);
}

void cds_lfq_init_rcu(struct cds_lfq_queue_rcu *q,
		      void (*release)(struct urcu_ref *ref))
{
	_cds_lfq_init_rcu(q, release);
}

void cds_lfq_enqueue_rcu(struct cds_lfq_queue_rcu *q, struct cds_lfq_node_rcu *node)
{
	_cds_lfq_enqueue_rcu(q, node);
}

struct cds_lfq_node_rcu *
cds_lfq_dequeue_rcu(struct cds_lfq_queue_rcu *q)
{
	return _cds_lfq_dequeue_rcu(q);
}
