#ifndef _URCU_RCULFQUEUE_H
#define _URCU_RCULFQUEUE_H

/*
 * rculfqueue.h
 *
 * Userspace RCU library - Lock-Free RCU Queue
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

#include <assert.h>
#include <urcu-call-rcu.h>

#ifdef __cplusplus
extern "C" {
#endif

struct cds_lfq_queue_rcu;

struct cds_lfq_node_rcu {
	struct cds_lfq_node_rcu *next;
	int dummy;
};

struct cds_lfq_queue_rcu {
	struct cds_lfq_node_rcu *head, *tail;
};

#ifdef _LGPL_SOURCE

#include <urcu/static/rculfqueue.h>

#define cds_lfq_node_init_rcu_qsbr	_cds_lfq_node_init_rcu
#define cds_lfq_init_rcu_qsbr		_cds_lfq_init_rcu
#define cds_lfq_destroy_rcu_qsbr	_cds_lfq_destroy_rcu
#define cds_lfq_enqueue_rcu_qsbr	_cds_lfq_enqueue_rcu
#define cds_lfq_dequeue_rcu_qsbr	_cds_lfq_dequeue_rcu

#define cds_lfq_node_init_rcu_bp	_cds_lfq_node_init_rcu
#define cds_lfq_init_rcu_bp		_cds_lfq_init_rcu
#define cds_lfq_destroy_rcu_bp		_cds_lfq_destroy_rcu
#define cds_lfq_enqueue_rcu_bp		_cds_lfq_enqueue_rcu
#define cds_lfq_dequeue_rcu_bp		_cds_lfq_dequeue_rcu

#define cds_lfq_node_init_rcu_memb	_cds_lfq_node_init_rcu
#define cds_lfq_init_rcu_memb		_cds_lfq_init_rcu
#define cds_lfq_destroy_rcu_memb	_cds_lfq_destroy_rcu
#define cds_lfq_enqueue_rcu_memb	_cds_lfq_enqueue_rcu
#define cds_lfq_dequeue_rcu_memb	_cds_lfq_dequeue_rcu

#define cds_lfq_node_init_rcu_mb	_cds_lfq_node_init_rcu
#define cds_lfq_init_rcu_mb		_cds_lfq_init_rcu
#define cds_lfq_destroy_rcu_mb		_cds_lfq_destroy_rcu
#define cds_lfq_enqueue_rcu_mb		_cds_lfq_enqueue_rcu
#define cds_lfq_dequeue_rcu_mb		_cds_lfq_dequeue_rcu

#define cds_lfq_node_init_rcu_sig	_cds_lfq_node_init_rcu
#define cds_lfq_init_rcu_sig		_cds_lfq_init_rcu
#define cds_lfq_destroy_rcu_sig		_cds_lfq_destroy_rcu
#define cds_lfq_enqueue_rcu_sig		_cds_lfq_enqueue_rcu
#define cds_lfq_dequeue_rcu_sig		_cds_lfq_dequeue_rcu

#else /* !_LGPL_SOURCE */

extern void cds_lfq_node_init_rcu(struct cds_lfq_node_rcu *node);
extern void cds_lfq_init_rcu(struct cds_lfq_queue_rcu *q);
/*
 * The queue should be emptied before calling destroy.
 *
 * Return 0 on success, -EPERM if queue is not empty.
 */
extern int cds_lfq_destroy_rcu(struct cds_lfq_queue_rcu *q);

/*
 * Acts as a RCU reader.
 */
extern void cds_lfq_enqueue_rcu(struct cds_lfq_queue_rcu *q,
				struct cds_lfq_node_rcu *node);

/*
 * Acts as a RCU reader.
 *
 * The caller must wait for a grace period to pass before freeing the returned
 * node or modifying the cds_lfq_node_rcu structure.
 * Returns NULL if queue is empty.
 */
extern
struct cds_lfq_node_rcu *cds_lfq_dequeue_rcu(struct cds_lfq_queue_rcu *q);

#endif /* !_LGPL_SOURCE */

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFQUEUE_H */
