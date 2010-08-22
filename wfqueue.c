/*
 * wfqueue.c
 *
 * Userspace RCU library - Queue with Wait-Free Enqueue/Blocking Dequeue
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

/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include "urcu/wfqueue.h"
#include "urcu/wfqueue-static.h"

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

void wfq_node_init(struct wfq_node *node)
{
	_wfq_node_init(node);
}

void wfq_init(struct wfq_queue *q)
{
	_wfq_init(q);
}

void wfq_enqueue(struct wfq_queue *q, struct wfq_node *node)
{
	_wfq_enqueue(q, node);
}

struct wfq_node *__wfq_dequeue_blocking(struct wfq_queue *q)
{
	return ___wfq_dequeue_blocking(q);
}

struct wfq_node *wfq_dequeue_blocking(struct wfq_queue *q)
{
	return _wfq_dequeue_blocking(q);
}
