/*
 * wfstack.c
 *
 * Userspace RCU library - Stack with Wait-Free push, Blocking pop.
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
#include "urcu/wfstack.h"
#include "urcu/wfstack-static.h"

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

void wfs_node_init(struct wfs_node *node)
{
	_wfs_node_init(node);
}

void wfs_init(struct wfs_stack *s)
{
	_wfs_init(s);
}

void wfs_push(struct wfs_stack *s, struct wfs_node *node)
{
	_wfs_push(s, node);
}

struct wfs_node *__wfs_pop_blocking(struct wfs_stack *s)
{
	return ___wfs_pop_blocking(s);
}

struct wfs_node *wfs_pop_blocking(struct wfs_stack *s)
{
	return _wfs_pop_blocking(s);
}
