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

struct cds_wfq_node {
	struct cds_wfq_node *next;
};

struct cds_wfq_queue {
	struct cds_wfq_node *head, **tail;
	struct cds_wfq_node dummy;	/* Dummy node */
	pthread_mutex_t lock;
};

#ifdef _LGPL_SOURCE

#include <urcu/static/wfqueue.h>

#define cds_wfq_node_init		_cds_wfq_node_init
#define cds_wfq_init		_cds_wfq_init
#define cds_wfq_enqueue		_cds_wfq_enqueue
#define __cds_wfq_dequeue_blocking	___cds_wfq_dequeue_blocking
#define cds_wfq_dequeue_blocking	_cds_wfq_dequeue_blocking

#else /* !_LGPL_SOURCE */

extern void cds_wfq_node_init(struct cds_wfq_node *node);
extern void cds_wfq_init(struct cds_wfq_queue *q);
extern void cds_wfq_enqueue(struct cds_wfq_queue *q, struct cds_wfq_node *node);
/* __cds_wfq_dequeue_blocking: caller ensures mutual exclusion between dequeues */
extern struct cds_wfq_node *__cds_wfq_dequeue_blocking(struct cds_wfq_queue *q);
extern struct cds_wfq_node *cds_wfq_dequeue_blocking(struct cds_wfq_queue *q);

#endif /* !_LGPL_SOURCE */

#ifdef __cplusplus
}
#endif

#endif /* _URCU_WFQUEUE_H */
