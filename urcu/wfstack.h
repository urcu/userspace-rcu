#ifndef _URCU_WFSTACK_H
#define _URCU_WFSTACK_H

/*
 * wfstack.h
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

#include <pthread.h>
#include <assert.h>
#include <urcu/compiler.h>

#ifdef __cplusplus
extern "C" {
#endif

struct cds_wfs_node {
	struct cds_wfs_node *next;
};

struct cds_wfs_stack {
	struct cds_wfs_node *head;
	pthread_mutex_t lock;
};

#ifdef _LGPL_SOURCE

#include <urcu/static/wfstack.h>

#define cds_wfs_node_init		_cds_wfs_node_init
#define cds_wfs_init		_cds_wfs_init
#define cds_wfs_push		_cds_wfs_push
#define __cds_wfs_pop_blocking	___cds_wfs_pop_blocking
#define cds_wfs_pop_blocking	_cds_wfs_pop_blocking

#else /* !_LGPL_SOURCE */

extern void cds_wfs_node_init(struct cds_wfs_node *node);
extern void cds_wfs_init(struct cds_wfs_stack *s);
extern int cds_wfs_push(struct cds_wfs_stack *s, struct cds_wfs_node *node);
/* __cds_wfs_pop_blocking: caller ensures mutual exclusion between pops */
extern struct cds_wfs_node *__cds_wfs_pop_blocking(struct cds_wfs_stack *s);
extern struct cds_wfs_node *cds_wfs_pop_blocking(struct cds_wfs_stack *s);

#endif /* !_LGPL_SOURCE */

#ifdef __cplusplus
}
#endif

#endif /* _URCU_WFSTACK_H */
