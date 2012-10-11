#ifndef _URCU_LFSTACK_H
#define _URCU_LFSTACK_H

/*
 * lfstack.h
 *
 * Userspace RCU library - Lock-Free Stack
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

#ifdef __cplusplus
extern "C" {
#endif

struct cds_lfs_node {
	struct cds_lfs_node *next;
};

struct cds_lfs_stack {
	struct cds_lfs_node *head;
};

#ifdef _LGPL_SOURCE

#include <urcu/static/lfstack.h>

#define cds_lfs_node_init		_cds_lfs_node_init
#define cds_lfs_init			_cds_lfs_init
#define cds_lfs_push			_cds_lfs_push
#define cds_lfs_pop			_cds_lfs_pop

#else /* !_LGPL_SOURCE */

extern void cds_lfs_node_init(struct cds_lfs_node *node);
extern void cds_lfs_init(struct cds_lfs_stack *s);

/*
 * cds_lfs_push: push a node into the stack.
 *
 * Does not require any synchronization with other push nor pop.
 *
 * Returns 0 if the stack was empty prior to adding the node.
 * Returns non-zero otherwise.
 */
extern int cds_lfs_push(struct cds_lfs_stack *s,
			struct cds_lfs_node *node);

/*
 * cds_lfs_pop: pop a node from the stack.
 *
 * Returns NULL if stack is empty.
 *
 * cds_lfs_pop needs to be synchronized using one of the following
 * techniques:
 *
 * 1) Calling cds_lfs_pop under rcu read lock critical section. The
 *    caller must wait for a grace period to pass before freeing the
 *    returned node or modifying the cds_lfs_node structure.
 * 2) Using mutual exclusion (e.g. mutexes) to protect cds_lfs_pop
 *    callers.
 * 3) Ensuring that only ONE thread can call cds_lfs_pop().
 *    (multi-provider/single-consumer scheme).
 */
extern struct cds_lfs_node *cds_lfs_pop(struct cds_lfs_stack *s);

#endif /* !_LGPL_SOURCE */

#ifdef __cplusplus
}
#endif

#endif /* _URCU_LFSTACK_H */
