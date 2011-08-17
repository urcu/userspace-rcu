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
#define _LGPL_SOURCE

#ifdef RCU_QSBR
# include "urcu-qsbr.h"
#elif defined(RCU_BP)
# include "urcu-bp.h"
#else
# include "urcu.h"
#endif

#undef _LGPL_SOURCE
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include "urcu/rculfstack.h"
#include "urcu/static/rculfstack.h"

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */


void cds_lfs_node_init_rcu(struct cds_lfs_node_rcu *node)
{
	_cds_lfs_node_init_rcu(node);
}

void cds_lfs_init_rcu(struct cds_lfs_stack_rcu *s)
{
	_cds_lfs_init_rcu(s);
}

void cds_lfs_push_rcu(struct cds_lfs_stack_rcu *s, struct cds_lfs_node_rcu *node)
{
	_cds_lfs_push_rcu(s, node);
}

struct cds_lfs_node_rcu *cds_lfs_pop_rcu(struct cds_lfs_stack_rcu *s)
{
	return _cds_lfs_pop_rcu(s);
}
