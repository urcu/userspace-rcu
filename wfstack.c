/*
 * wfstack.c
 *
 * Userspace RCU library - Stack with wait-free push, blocking traversal.
 *
 * Copyright 2010-2012 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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
#include "urcu/static/wfstack.h"

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

void cds_wfs_node_init(struct cds_wfs_node *node)
{
	_cds_wfs_node_init(node);
}

void cds_wfs_init(struct cds_wfs_stack *s)
{
	_cds_wfs_init(s);
}

void cds_wfs_destroy(struct cds_wfs_stack *s)
{
	_cds_wfs_destroy(s);
}

void __cds_wfs_init(struct __cds_wfs_stack *s)
{
	___cds_wfs_init(s);
}

bool cds_wfs_empty(cds_wfs_stack_ptr_t u_stack)
{
	return _cds_wfs_empty(u_stack);
}

int cds_wfs_push(cds_wfs_stack_ptr_t u_stack, struct cds_wfs_node *node)
{
	return _cds_wfs_push(u_stack, node);
}

struct cds_wfs_node *cds_wfs_pop_blocking(struct cds_wfs_stack *s)
{
	return _cds_wfs_pop_blocking(s);
}

struct cds_wfs_node *
	cds_wfs_pop_with_state_blocking(struct cds_wfs_stack *s, int *state)
{
	return _cds_wfs_pop_with_state_blocking(s, state);
}

struct cds_wfs_head *cds_wfs_pop_all_blocking(struct cds_wfs_stack *s)
{
	return _cds_wfs_pop_all_blocking(s);
}

struct cds_wfs_node *cds_wfs_first(struct cds_wfs_head *head)
{
	return _cds_wfs_first(head);
}

struct cds_wfs_node *cds_wfs_next_blocking(struct cds_wfs_node *node)
{
	return _cds_wfs_next_blocking(node);
}

struct cds_wfs_node *cds_wfs_next_nonblocking(struct cds_wfs_node *node)
{
	return _cds_wfs_next_nonblocking(node);
}

void cds_wfs_pop_lock(struct cds_wfs_stack *s)
{
	_cds_wfs_pop_lock(s);
}

void cds_wfs_pop_unlock(struct cds_wfs_stack *s)
{
	_cds_wfs_pop_unlock(s);
}

struct cds_wfs_node *__cds_wfs_pop_blocking(cds_wfs_stack_ptr_t u_stack)
{
	return ___cds_wfs_pop_blocking(u_stack);
}

struct cds_wfs_node *
	__cds_wfs_pop_with_state_blocking(cds_wfs_stack_ptr_t u_stack,
		int *state)
{
	return ___cds_wfs_pop_with_state_blocking(u_stack, state);
}

struct cds_wfs_node *__cds_wfs_pop_nonblocking(cds_wfs_stack_ptr_t u_stack)
{
	return ___cds_wfs_pop_nonblocking(u_stack);
}

struct cds_wfs_node *
	__cds_wfs_pop_with_state_nonblocking(cds_wfs_stack_ptr_t u_stack,
		int *state)
{
	return ___cds_wfs_pop_with_state_nonblocking(u_stack, state);
}

struct cds_wfs_head *__cds_wfs_pop_all(cds_wfs_stack_ptr_t u_stack)
{
	return ___cds_wfs_pop_all(u_stack);
}
