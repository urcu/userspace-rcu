#ifndef _URCU_WORKQUEUE_FIFO_H
#define _URCU_WORKQUEUE_FIFO_H

/*
 * urcu/workqueue-fifo.h
 *
 * Userspace RCU library - work queue scheme with FIFO semantic
 *
 * Copyright (c) 2014 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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

#include <urcu/uatomic.h>
#include <urcu/wfstack.h>
#include <urcu/waitqueue-lifo.h>
#include <urcu/wfcqueue.h>
#include <urcu/rculist.h>
#include <pthread.h>

/*
 * We use RCU to steal work from siblings. Therefore, one of RCU flavors
 * need to be included before this header. All worker that participate
 * in stealing (initialized with the URCU_WORKER_STEAL flag) need to be
 * registered RCU readers threads.
 */

struct urcu_work {
	struct cds_wfcq_node node;
};

struct urcu_workqueue {
	/* FIFO work queue */
	struct __cds_wfcq_head head;
	struct cds_wfcq_tail tail;

	/* Associated wait queue for LIFO wait/wakeup */
	struct urcu_wait_queue waitqueue;

	/* RCU linked list head of siblings for work stealing. */
	struct cds_list_head sibling_head;
	pthread_mutex_t sibling_lock;	/* Protect sibling list updates */
};

struct urcu_worker {
	struct cds_wfcq_head head;
	struct cds_wfcq_tail tail;

	struct urcu_wait_node wait_node;
	/* RCU linked list node of siblings for work stealing. */
	struct cds_list_head sibling_node;
	int flags;	/* enum urcu_worker_flags */
};

enum urcu_worker_flags {
	URCU_WORKER_STEAL	= (1 << 0),
};

static inline
void urcu_workqueue_init(struct urcu_workqueue *queue)
{
	__cds_wfcq_init(&queue->head, &queue->tail);
	urcu_wait_queue_init(&queue->waitqueue);
	CDS_INIT_LIST_HEAD(&queue->sibling_head);
}

static inline
void urcu_queue_work(struct urcu_workqueue *queue, struct urcu_work *work)
{
	bool was_empty;

	cds_wfcq_node_init(&work->node);

	/* Enqueue work. */
	was_empty = !cds_wfcq_enqueue(&queue->head, &queue->tail,
			&work->node);
	/*
	 * If workqueue was previously empty, wakeup one worker thread.
	 * It will eventually grab the entire content of the work-queue
	 * (therefore grabbing a "work batch"). After having grabbed the
	 * work batch, while that thread is running and taking care of
	 * that work batch, when we enqueue more work, we will wake
	 * another thread (if there is one waiting), which will
	 * eventually grab the new batch, and so on. This scheme ensures
	 * that contiguous batch of work are handled by the same thread
	 * (for locality), and also ensures that we scale work to many
	 * worker threads when threads are busy enough to still be
	 * running when work is enqueued.
	 */
	if (was_empty)
		(void) urcu_dequeue_wake_single(&queue->waitqueue);
}

static inline
void urcu_workqueue_wakeup_all(struct urcu_workqueue *queue)
{
	struct urcu_waiters waiters;

	urcu_move_waiters(&waiters, &queue->waitqueue);
	(void) urcu_wake_all_waiters(&waiters);
}

static inline
void urcu_worker_init(struct urcu_worker *worker, int flags)
{
	cds_wfcq_init(&worker->head, &worker->tail);
	worker->flags = flags;
	urcu_wait_node_init(&worker->wait_node, URCU_WAIT_RUNNING);
}

static inline
void urcu_worker_register(struct urcu_workqueue *queue,
		struct urcu_worker *worker)
{
	if (worker->flags & URCU_WORKER_STEAL) {
		pthread_mutex_lock(&queue->sibling_lock);
		cds_list_add_rcu(&worker->sibling_node, &queue->sibling_head);
		pthread_mutex_unlock(&queue->sibling_lock);
	}
}

static inline
void urcu_worker_unregister(struct urcu_workqueue *queue,
		struct urcu_worker *worker)
{
	enum cds_wfcq_ret wfcq_ret;

	if (worker->flags & URCU_WORKER_STEAL) {
		pthread_mutex_lock(&queue->sibling_lock);
		cds_list_del_rcu(&worker->sibling_node);
		pthread_mutex_unlock(&queue->sibling_lock);

		/*
		 * Wait for grace period before freeing or reusing
		 * "worker" because used by RCU linked list.
		 */
		synchronize_rcu();
	}

	/*
	 * Put any local work we still have back into the workqueue.
	 */
	wfcq_ret = __cds_wfcq_splice_blocking(&queue->head,
			&queue->tail,
			&worker->head,
			&worker->tail);
	if (wfcq_ret != CDS_WFCQ_RET_SRC_EMPTY
			&& wfcq_ret == CDS_WFCQ_RET_DEST_EMPTY) {
		/*
		 * Wakeup worker thread if we have put work back into
		 * workqueue that was previously empty.
		 */
		(void) urcu_dequeue_wake_single(&queue->waitqueue);
	}
}

/*
 * Try stealing work from siblings when we have nothing to do.
 */
static inline
void ___urcu_steal_work(struct urcu_worker *worker,
		struct urcu_worker *sibling)
{
	/*
	 * Don't bother grabbing the sibling queue lock if it is empty.
	 */
	if (cds_wfcq_empty(&sibling->head, &sibling->tail))
		return;
	cds_wfcq_dequeue_lock(&sibling->head, &sibling->tail);
	(void) __cds_wfcq_splice_blocking(&worker->head,
			&worker->tail,
			&sibling->head,
			&sibling->tail);
	cds_wfcq_dequeue_unlock(&sibling->head, &sibling->tail);
}

static inline
int __urcu_steal_work(struct urcu_workqueue *queue,
		struct urcu_worker *worker)
{
	struct urcu_worker *sibling_prev, *sibling_next;
	struct cds_list_head *sibling_node;

	if (!(worker->flags & URCU_WORKER_STEAL))
		return 0;

	rcu_read_lock();

	sibling_node = rcu_dereference(worker->sibling_node.next);
	if (sibling_node == &queue->sibling_head)
		sibling_node = rcu_dereference(sibling_node->next);
	sibling_next = caa_container_of(sibling_node, struct urcu_worker,
			sibling_node);
	if (sibling_next != worker)
		___urcu_steal_work(worker, sibling_next);

	sibling_node = rcu_dereference(worker->sibling_node.prev);
	if (sibling_node == &queue->sibling_head)
		sibling_node = rcu_dereference(sibling_node->prev);
	sibling_prev = caa_container_of(sibling_node, struct urcu_worker,
			sibling_node);
	if (sibling_prev != worker && sibling_prev != sibling_next)
		___urcu_steal_work(worker, sibling_prev);

	rcu_read_unlock();

	return !cds_wfcq_empty(&worker->head, &worker->tail);
}

static inline
bool ___urcu_wakeup_sibling(struct urcu_worker *sibling)
{
	return urcu_adaptative_wake_up(&sibling->wait_node);
}

static inline
bool __urcu_wakeup_siblings(struct urcu_workqueue *queue,
		struct urcu_worker *worker)
{
	struct urcu_worker *sibling_prev, *sibling_next;
	struct cds_list_head *sibling_node;
	bool wakeup_performed = 0;

	if (!(worker->flags & URCU_WORKER_STEAL))
		return;

	/* Only wakeup siblings if we have work in our own queue. */
	if (cds_wfcq_empty(&worker->head, &worker->tail))
		return;

	rcu_read_lock();

	sibling_node = rcu_dereference(worker->sibling_node.next);
	if (sibling_node == &queue->sibling_head)
		sibling_node = rcu_dereference(sibling_node->next);
	sibling_next = caa_container_of(sibling_node, struct urcu_worker,
			sibling_node);
	if (sibling_next != worker)
		wakeup_performed = ___urcu_wakeup_sibling(sibling_next);
	if (wakeup_performed)
		goto end;

	sibling_node = rcu_dereference(worker->sibling_node.prev);
	if (sibling_node == &queue->sibling_head)
		sibling_node = rcu_dereference(sibling_node->prev);
	sibling_prev = caa_container_of(sibling_node, struct urcu_worker,
			sibling_node);
	if (sibling_prev != worker && sibling_prev != sibling_next)
		wakeup_performed = ___urcu_wakeup_sibling(sibling_prev);
end:
	rcu_read_unlock();

	return wakeup_performed;
}

static inline
void urcu_accept_work(struct urcu_workqueue *queue,
		struct urcu_worker *worker,
		int blocking)
{
	enum cds_wfcq_ret wfcq_ret;

	wfcq_ret = __cds_wfcq_splice_blocking(&worker->head,
			&worker->tail,
			&queue->head,
			&queue->tail);
	/* Don't wait if we have work to do. */
	if (wfcq_ret != CDS_WFCQ_RET_SRC_EMPTY
			|| !cds_wfcq_empty(&worker->head,
				&worker->tail))
		goto do_work;
	/* Try to steal work from sibling instead of blocking */
	if (__urcu_steal_work(queue, worker))
		goto do_work;
	if (!blocking)
		return;
	urcu_wait_set_state(&worker->wait_node,
			URCU_WAIT_WAITING);
	if (!CMM_LOAD_SHARED(worker->wait_node.node.next)) {
		int was_empty;

		/*
		 * NULL next pointer. We are therefore not in
		 * the queue.
		 */
		cds_wfs_node_init(&worker->wait_node.node);
		was_empty = !urcu_wait_add(&queue->waitqueue,
				&worker->wait_node);
		/*
		 * If the wait queue was empty, it means we are the
		 * first thread to be put back into an otherwise empty
		 * wait queue. Re-check if work queue is empty after
		 * adding ourself to wait queue, so we can wakeup the
		 * top of wait queue since new work have appeared, and
		 * work enqueuer may not have seen that it needed to do
		 * a wake up.
		 */
		if (was_empty && !cds_wfcq_empty(&queue->head,
						&queue->tail))
			(void) urcu_dequeue_wake_single(&queue->waitqueue);
	} else {
		/*
		 * Non-NULL next pointer. We are therefore in
		 * the queue, or the dispatcher just removed us
		 * from it (after we read the next pointer), and
		 * is therefore awakening us. The state will
		 * therefore have been changed from WAITING to
		 * some other state, which will let the busy
		 * wait pass through.
		 */
	}
	urcu_adaptative_busy_wait(&worker->wait_node);
	return;

do_work:
	/*
	 * We will be busy handling the work batch, awaken siblings so
	 * they can steal from us.
	 */
	(void) __urcu_wakeup_siblings(queue, worker);
}

static inline
struct urcu_work *urcu_dequeue_work(struct urcu_worker *worker)
{
	struct cds_wfcq_node *node;

	/*
	 * If we are registered for work stealing, we need to dequeue
	 * safely against siblings.
	 */
	if (worker->flags & URCU_WORKER_STEAL) {
		/*
		 * Don't bother grabbing the worker queue lock if it is
		 * empty.
		 */
		if (cds_wfcq_empty(&worker->head, &worker->tail))
			return NULL;
		node = cds_wfcq_dequeue_blocking(&worker->head,
				&worker->tail);
	} else {
		node = ___cds_wfcq_dequeue_with_state(&worker->head,
				&worker->tail, NULL, 1, 0);
	}
	if (!node)
		return NULL;
	return caa_container_of(node, struct urcu_work, node);
}

#endif /* _URCU_WORKQUEUE_FIFO_H */
