#ifndef _URCU_WFCQUEUE_H
#define _URCU_WFCQUEUE_H

/*
 * wfcqueue.h
 *
 * Userspace RCU library - Concurrent Queue with Wait-Free Enqueue/Blocking Dequeue
 *
 * Copyright 2010-2012 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 * Copyright 2011-2012 - Lai Jiangshan <laijs@cn.fujitsu.com>
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
#include <stdbool.h>
#include <urcu/compiler.h>
#include <urcu/arch.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Concurrent queue with wait-free enqueue/blocking dequeue.
 *
 * Inspired from half-wait-free/half-blocking queue implementation done by
 * Paul E. McKenney.
 */

struct cds_wfcq_node {
	struct cds_wfcq_node *next;
};

/*
 * Do not put head and tail on the same cache-line if concurrent
 * enqueue/dequeue are expected from many CPUs. This eliminates
 * false-sharing between enqueue and dequeue.
 */
struct cds_wfcq_head {
	struct cds_wfcq_node node;
	pthread_mutex_t lock;
};

struct cds_wfcq_tail {
	struct cds_wfcq_node *p;
};

#ifdef _LGPL_SOURCE

#include <urcu/static/wfcqueue.h>

#define cds_wfcq_node_init		_cds_wfcq_node_init
#define cds_wfcq_init			_cds_wfcq_init
#define cds_wfcq_empty			_cds_wfcq_empty
#define cds_wfcq_enqueue		_cds_wfcq_enqueue

/* Dequeue locking */
#define cds_wfcq_dequeue_lock		_cds_wfcq_dequeue_lock
#define cds_wfcq_dequeue_unlock		_cds_wfcq_dequeue_unlock

/* Locking performed within cds_wfcq calls. */
#define cds_wfcq_dequeue_blocking	_cds_wfcq_dequeue_blocking
#define cds_wfcq_splice_blocking	_cds_wfcq_splice_blocking
#define cds_wfcq_first_blocking		_cds_wfcq_first_blocking
#define cds_wfcq_next_blocking		_cds_wfcq_next_blocking

/* Locking ensured by caller by holding cds_wfcq_dequeue_lock() */
#define __cds_wfcq_dequeue_blocking	___cds_wfcq_dequeue_blocking
#define __cds_wfcq_splice_blocking	___cds_wfcq_splice_blocking
#define __cds_wfcq_first_blocking	___cds_wfcq_first_blocking
#define __cds_wfcq_next_blocking	___cds_wfcq_next_blocking

#else /* !_LGPL_SOURCE */

/*
 * Mutual exclusion of cds_wfcq_* / __cds_wfcq_* API
 *
 * Unless otherwise stated, the caller must ensure mutual exclusion of
 * queue update operations "dequeue" and "splice" (for source queue).
 * Queue read operations "first" and "next", which are used by
 * "for_each" iterations, need to be protected against concurrent
 * "dequeue" and "splice" (for source queue) by the caller.
 * "enqueue", "splice" (for destination queue), and "empty" are the only
 * operations that can be used without any mutual exclusion.
 * Mutual exclusion can be ensured by holding cds_wfcq_dequeue_lock().
 *
 * For convenience, cds_wfcq_dequeue_blocking() and
 * cds_wfcq_splice_blocking() hold the dequeue lock.
 */

/*
 * cds_wfcq_node_init: initialize wait-free queue node.
 */
extern void cds_wfcq_node_init(struct cds_wfcq_node *node);

/*
 * cds_wfcq_init: initialize wait-free queue.
 */
extern void cds_wfcq_init(struct cds_wfcq_head *head,
		struct cds_wfcq_tail *tail);

/*
 * cds_wfcq_empty: return whether wait-free queue is empty.
 *
 * No memory barrier is issued. No mutual exclusion is required.
 */
extern bool cds_wfcq_empty(struct cds_wfcq_head *head,
		struct cds_wfcq_tail *tail);

/*
 * cds_wfcq_dequeue_lock: take the dequeue mutual exclusion lock.
 */
extern void cds_wfcq_dequeue_lock(struct cds_wfcq_head *head,
		struct cds_wfcq_tail *tail);

/*
 * cds_wfcq_dequeue_unlock: release the dequeue mutual exclusion lock.
 */
extern void cds_wfcq_dequeue_unlock(struct cds_wfcq_head *head,
		struct cds_wfcq_tail *tail);

/*
 * cds_wfcq_enqueue: enqueue a node into a wait-free queue.
 *
 * Issues a full memory barrier before enqueue. No mutual exclusion is
 * required.
 */
extern void cds_wfcq_enqueue(struct cds_wfcq_head *head,
		struct cds_wfcq_tail *tail,
		struct cds_wfcq_node *node);

/*
 * cds_wfcq_dequeue_blocking: dequeue a node from a wait-free queue.
 *
 * Content written into the node before enqueue is guaranteed to be
 * consistent, but no other memory ordering is ensured.
 * It is valid to reuse and free a dequeued node immediately.
 * Mutual exlusion with dequeuers is ensured internally.
 */
extern struct cds_wfcq_node *cds_wfcq_dequeue_blocking(
		struct cds_wfcq_head *head,
		struct cds_wfcq_tail *tail);

/*
 * cds_wfcq_splice_blocking: enqueue all src_q nodes at the end of dest_q.
 *
 * Dequeue all nodes from src_q.
 * dest_q must be already initialized.
 * Content written into the node before enqueue is guaranteed to be
 * consistent, but no other memory ordering is ensured.
 * Mutual exlusion with dequeuers is ensured internally.
 */
extern void cds_wfcq_splice_blocking(
		struct cds_wfcq_head *dest_q_head,
		struct cds_wfcq_tail *dest_q_tail,
		struct cds_wfcq_head *src_q_head,
		struct cds_wfcq_tail *src_q_tail);

/*
 * __cds_wfcq_dequeue_blocking:
 *
 * Content written into the node before enqueue is guaranteed to be
 * consistent, but no other memory ordering is ensured.
 * It is valid to reuse and free a dequeued node immediately.
 * Should be called with cds_wfcq_dequeue_lock() held.
 */
extern struct cds_wfcq_node *__cds_wfcq_dequeue_blocking(
		struct cds_wfcq_head *head,
		struct cds_wfcq_tail *tail);

/*
 * __cds_wfcq_splice_blocking: enqueue all src_q nodes at the end of dest_q.
 *
 * Dequeue all nodes from src_q.
 * dest_q must be already initialized.
 * Content written into the node before enqueue is guaranteed to be
 * consistent, but no other memory ordering is ensured.
 * Should be called with cds_wfcq_dequeue_lock() held.
 */
extern void __cds_wfcq_splice_blocking(
		struct cds_wfcq_head *dest_q_head,
		struct cds_wfcq_tail *dest_q_tail,
		struct cds_wfcq_head *src_q_head,
		struct cds_wfcq_tail *src_q_tail);

/*
 * __cds_wfcq_first_blocking: get first node of a queue, without dequeuing.
 *
 * Content written into the node before enqueue is guaranteed to be
 * consistent, but no other memory ordering is ensured.
 * Should be called with cds_wfcq_dequeue_lock() held.
 *
 * Used by for-like iteration macros:
 * __cds_wfcq_for_each_blocking()
 * __cds_wfcq_for_each_blocking_safe()
 */
extern struct cds_wfcq_node *__cds_wfcq_first_blocking(
		struct cds_wfcq_head *head,
		struct cds_wfcq_tail *tail);

/*
 * __cds_wfcq_next_blocking: get next node of a queue, without dequeuing.
 *
 * Content written into the node before enqueue is guaranteed to be
 * consistent, but no other memory ordering is ensured.
 * Should be called with cds_wfcq_dequeue_lock() held.
 *
 * Used by for-like iteration macros:
 * __cds_wfcq_for_each_blocking()
 * __cds_wfcq_for_each_blocking_safe()
 */
extern struct cds_wfcq_node *__cds_wfcq_next_blocking(
		struct cds_wfcq_head *head,
		struct cds_wfcq_tail *tail,
		struct cds_wfcq_node *node);

#endif /* !_LGPL_SOURCE */

/*
 * __cds_wfcq_for_each_blocking: Iterate over all nodes in a queue,
 * without dequeuing them.
 * @head: head of the queue (struct cds_wfcq_head pointer).
 * @tail: tail of the queue (struct cds_wfcq_tail pointer).
 * @node: iterator on the queue (struct cds_wfcq_node pointer).
 *
 * Content written into each node before enqueue is guaranteed to be
 * consistent, but no other memory ordering is ensured.
 * Should be called with cds_wfcq_dequeue_lock() held.
 */
#define __cds_wfcq_for_each_blocking(head, tail, node)		\
	for (node = __cds_wfcq_first_blocking(head, tail);	\
		node != NULL;					\
		node = __cds_wfcq_next_blocking(head, tail, node))

/*
 * __cds_wfcq_for_each_blocking_safe: Iterate over all nodes in a queue,
 * without dequeuing them. Safe against deletion.
 * @head: head of the queue (struct cds_wfcq_head pointer).
 * @tail: tail of the queue (struct cds_wfcq_tail pointer).
 * @node: iterator on the queue (struct cds_wfcq_node pointer).
 * @n: struct cds_wfcq_node pointer holding the next pointer (used
 *     internally).
 *
 * Content written into each node before enqueue is guaranteed to be
 * consistent, but no other memory ordering is ensured.
 * Should be called with cds_wfcq_dequeue_lock() held.
 */
#define __cds_wfcq_for_each_blocking_safe(head, tail, node, n)		       \
	for (node = __cds_wfcq_first_blocking(head, tail),		       \
			n = (node ? __cds_wfcq_next_blocking(head, tail, node) : NULL); \
		node != NULL;						       \
		node = n, n = (node ? __cds_wfcq_next_blocking(head, tail, node) : NULL))

#ifdef __cplusplus
}
#endif

#endif /* _URCU_WFCQUEUE_H */
