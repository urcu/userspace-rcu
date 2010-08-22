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

struct wfs_node {
	struct wfs_node *next;
};

struct wfs_stack {
	struct wfs_node *head;
	pthread_mutex_t lock;
};

#ifdef _LGPL_SOURCE

#include <urcu/wfstack-static.h>

#define wfs_node_init		_wfs_node_init
#define wfs_init		_wfs_init
#define wfs_push		_wfs_push
#define __wfs_pop_blocking	___wfs_pop_blocking
#define wfs_pop_blocking	_wfs_pop_blocking

#else /* !_LGPL_SOURCE */

extern void wfs_node_init(struct wfs_node *node);
extern void wfs_init(struct wfs_stack *s);
extern void wfs_push(struct wfs_stack *s, struct wfs_node *node);
/* __wfs_pop_blocking: caller ensures mutual exclusion between pops */
extern struct wfs_node *__wfs_pop_blocking(struct wfs_stack *s);
extern struct wfs_node *wfs_pop_blocking(struct wfs_stack *s);

#endif /* !_LGPL_SOURCE */

#ifdef __cplusplus
}
#endif

#endif /* _URCU_WFSTACK_H */
