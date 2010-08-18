#ifndef _URCU_WFSTACK_H
#define _URCU_WFSTACK_H

/*
 * rcuwfstack.h
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

#if (!defined(_GNU_SOURCE) && !defined(_LGPL_SOURCE))
#error "Dynamic loader LGPL wrappers not implemented yet"
#endif

#define WF_STACK_END			((void *)0x1UL)
#define WFS_ADAPT_ATTEMPTS		10	/* Retry if being set */
#define WFS_WAIT			10	/* Wait 10 ms if being set */

struct wfs_node {
	struct wfs_node *next;
};

struct wfs_stack {
	struct wfs_node *head;
	pthread_mutex_t lock;
};

void wfs_node_init(struct wfs_node *node)
{
	node->next = NULL;
}

void wfs_init(struct wfs_stack *s)
{
	int ret;

	s->head = WF_STACK_END;
	ret = pthread_mutex_init(&s->lock, NULL);
	assert(!ret);
}

void wfs_push(struct wfs_stack *s, struct wfs_node *node)
{
	struct wfs_node *old_head;

	assert(node->next == NULL);
	/*
	 * uatomic_xchg() implicit memory barrier orders earlier stores to node
	 * (setting it to NULL) before publication.
	 */
	old_head = uatomic_xchg(&s->head, node);
	/*
	 * At this point, dequeuers see a NULL node->next, they should busy-wait
	 * until node->next is set to old_head.
	 */
	STORE_SHARED(node->next, old_head);
}

/*
 * Returns NULL if stack is empty.
 */
struct wfs_node *
__wfs_pop_blocking(struct wfs_stack *s)
{
	struct wfs_node *head, *next;
	int attempt = 0;

retry:
	head = LOAD_SHARED(s->head);
	if (head == WF_STACK_END)
		return NULL;
	/*
	 * Adaptative busy-looping waiting for push to complete.
	 */
	while ((next = LOAD_SHARED(head->next)) == NULL) {
		if (++attempt >= WFS_ADAPT_ATTEMPTS) {
			poll(NULL, 0, WFS_WAIT);	/* Wait for 10ms */
			attempt = 0;
		} else
			cpu_relax();
	}
	if (uatomic_cmpxchg(&s->head, head, next) == head)
		return head;
	else
		goto retry;		/* Concurrent modification. Retry. */
}

struct wfs_node *
wfs_pop_blocking(struct wfs_stack *s)
{
	struct wfs_node *retnode;
	int ret;

	ret = pthread_mutex_lock(&s->lock);
	assert(!ret);
	retnode = __wfs_pop_blocking(s);
	ret = pthread_mutex_unlock(&s->lock);
	assert(!ret);
	return retnode;
}

#ifdef __cplusplus
}
#endif

#endif /* _URCU_WFSTACK_H */
