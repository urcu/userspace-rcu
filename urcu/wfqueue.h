#ifndef _URCU_WFQUEUE_H
#define _URCU_WFQUEUE_H

/*
 * wfqueue.h
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

#include <pthread.h>
#include <assert.h>
#include <urcu/compiler.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Queue with wait-free enqueue/blocking dequeue.
 * This implementation adds a dummy head node when the queue is empty to ensure
 * we can always update the queue locklessly.
 *
 * Inspired from half-wait-free/half-blocking queue implementation done by
 * Paul E. McKenney.
 */

struct wfq_node {
	struct wfq_node *next;
};

struct wfq_queue {
	struct wfq_node *head, **tail;
	struct wfq_node dummy;	/* Dummy node */
	pthread_mutex_t lock;
};

#ifdef _LGPL_SOURCE

#include <urcu/wfqueue-static.h>

#define wfq_node_init		_wfq_node_init
#define wfq_init		_wfq_init
#define wfq_enqueue		_wfq_enqueue
#define __wfq_dequeue_blocking	___wfq_dequeue_blocking
#define wfq_dequeue_blocking	_wfq_dequeue_blocking

#else /* !_LGPL_SOURCE */

extern void wfq_node_init(struct wfq_node *node);
extern void wfq_init(struct wfq_queue *q);
extern void wfq_enqueue(struct wfq_queue *q, struct wfq_node *node);
/* __wfq_dequeue_blocking: caller ensures mutual exclusion between dequeues */
extern struct wfq_node *__wfq_dequeue_blocking(struct wfq_queue *q);
extern struct wfq_node *wfq_dequeue_blocking(struct wfq_queue *q);

#endif /* !_LGPL_SOURCE */

#ifdef __cplusplus
}
#endif

#endif /* _URCU_WFQUEUE_H */
