#ifndef _URCU_WFSTACK_STATIC_H
#define _URCU_WFSTACK_STATIC_H

/*
 * wfstack-static.h
 *
 * Userspace RCU library - Stack with Wait-Free push, Blocking pop.
 *
 * TO BE INCLUDED ONLY IN LGPL-COMPATIBLE CODE. See wfstack.h for linking
 * dynamically with the userspace rcu library.
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
#include <poll.h>
#include <urcu/compiler.h>
#include <urcu/uatomic.h>

#ifdef __cplusplus
extern "C" {
#endif

#define CDS_WF_STACK_END			((void *)0x1UL)
#define CDS_WFS_ADAPT_ATTEMPTS		10	/* Retry if being set */
#define CDS_WFS_WAIT			10	/* Wait 10 ms if being set */

static inline
void _cds_wfs_node_init(struct cds_wfs_node *node)
{
	node->next = NULL;
}

static inline
void _cds_wfs_init(struct cds_wfs_stack *s)
{
	int ret;

	s->head = CDS_WF_STACK_END;
	ret = pthread_mutex_init(&s->lock, NULL);
	assert(!ret);
}

/*
 * Returns 0 if stack was empty, 1 otherwise.
 */
static inline
int _cds_wfs_push(struct cds_wfs_stack *s, struct cds_wfs_node *node)
{
	struct cds_wfs_node *old_head;

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
	CMM_STORE_SHARED(node->next, old_head);
	return (old_head != CDS_WF_STACK_END);
}

/*
 * Returns NULL if stack is empty.
 */
static inline
struct cds_wfs_node *
___cds_wfs_pop_blocking(struct cds_wfs_stack *s)
{
	struct cds_wfs_node *head, *next;
	int attempt = 0;

retry:
	head = CMM_LOAD_SHARED(s->head);
	if (head == CDS_WF_STACK_END)
		return NULL;
	/*
	 * Adaptative busy-looping waiting for push to complete.
	 */
	while ((next = CMM_LOAD_SHARED(head->next)) == NULL) {
		if (++attempt >= CDS_WFS_ADAPT_ATTEMPTS) {
			poll(NULL, 0, CDS_WFS_WAIT);	/* Wait for 10ms */
			attempt = 0;
		} else
			caa_cpu_relax();
	}
	if (uatomic_cmpxchg(&s->head, head, next) == head)
		return head;
	else
		goto retry;		/* Concurrent modification. Retry. */
}

static inline
struct cds_wfs_node *
_cds_wfs_pop_blocking(struct cds_wfs_stack *s)
{
	struct cds_wfs_node *retnode;
	int ret;

	ret = pthread_mutex_lock(&s->lock);
	assert(!ret);
	retnode = ___cds_wfs_pop_blocking(s);
	ret = pthread_mutex_unlock(&s->lock);
	assert(!ret);
	return retnode;
}

#ifdef __cplusplus
}
#endif

#endif /* _URCU_WFSTACK_STATIC_H */
