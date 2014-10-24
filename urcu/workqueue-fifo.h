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
#include <urcu/lfstack.h>
#include <urcu/waitqueue-lifo.h>
#include <urcu/wfcqueue.h>
#include <urcu/rculist.h>
#include <pthread.h>
#include <assert.h>

enum urcu_accept_ret {
	URCU_ACCEPT_WORK	= 0,
	URCU_ACCEPT_SHUTDOWN	= 1,
};

enum urcu_enqueue_ret {
	URCU_ENQUEUE_OK		= 0,
	URCU_ENQUEUE_FULL	= 1,
};

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

	/* Maximum number of work entries (approximate). 0 means infinite. */
	unsigned long nr_work_max;
	unsigned long nr_work;		/* Current number of work items */

	int worker_flags;		/* Worker flags */
	bool shutdown;			/* Shutdown performed */
};

struct urcu_worker {
	/* Workqueue which can be either used by worker, or stolen. */
	struct cds_wfcq_head head;
	struct cds_wfcq_tail tail;

	/* Work belonging to worker. Cannot be stolen. */
	struct urcu_work *own;

	struct urcu_wait_node wait_node;
	/* RCU linked list node of siblings for work stealing. */
	struct cds_list_head sibling_node;
	struct urcu_workqueue *queue;
	int flags;	/* enum urcu_worker_flags */
};

enum urcu_worker_flags {
	URCU_WORKER_STEAL	= (1 << 0),
};

static inline
void urcu_workqueue_init(struct urcu_workqueue *queue,
		unsigned long max_queue_len,
		int worker_flags)
{
	__cds_wfcq_init(&queue->head, &queue->tail);
	urcu_wait_queue_init(&queue->waitqueue);
	CDS_INIT_LIST_HEAD(&queue->sibling_head);
	pthread_mutex_init(&queue->sibling_lock, NULL);
	queue->nr_work_max = max_queue_len;
	queue->nr_work = 0;
	queue->shutdown = false;
}

static inline
enum urcu_enqueue_ret urcu_queue_work(struct urcu_workqueue *queue,
		struct urcu_work *work)
{
	bool was_empty;
	unsigned long nr_work_max;

	nr_work_max = queue->nr_work_max;
	if (nr_work_max) {
		/* Approximate max queue size. */
		if (uatomic_read(&queue->nr_work) >= nr_work_max)
			return URCU_ENQUEUE_FULL;
		uatomic_inc(&queue->nr_work);
	}
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
	if (was_empty) {
		rcu_read_lock();	/* Protect stack dequeue */
		(void) urcu_dequeue_wake_single(&queue->waitqueue);
		rcu_read_unlock();	/* Protect stack dequeue */
	}
	return URCU_ENQUEUE_OK;
}

static inline
void __urcu_workqueue_wakeup_all(struct urcu_workqueue *queue)
{
	struct urcu_waiters waiters;

	rcu_read_lock();	/* Protect stack dequeue */
	urcu_move_waiters(&waiters, &queue->waitqueue);
	rcu_read_unlock();	/* Protect stack dequeue */

	(void) urcu_wake_all_waiters(&waiters);
}

static inline
void urcu_worker_init(struct urcu_workqueue *queue,
		struct urcu_worker *worker)
{
	cds_wfcq_init(&worker->head, &worker->tail);
	urcu_wait_node_init(&worker->wait_node, URCU_WAIT_RUNNING);
	worker->own = NULL;
	worker->wait_node.node.next = NULL;
	worker->queue = queue;
	worker->flags = queue->worker_flags;
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
	}

	/*
	 * Make sure we are removed from waitqueue.
	 */
	if (CMM_LOAD_SHARED(worker->wait_node.node.next))
		__urcu_workqueue_wakeup_all(queue);

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
		rcu_read_lock();	/* Protect stack dequeue */
		(void) urcu_dequeue_wake_single(&queue->waitqueue);
		rcu_read_unlock();	/* Protect stack dequeue */
	}

	/*
	 * Wait for grace period before freeing or reusing
	 * "worker" because used by RCU linked list.
	 * Also prevents ABA for waitqueue stack dequeue: matches RCU
	 * read-side critical sections around dequeue and move all
	 * operations on waitqueue).
	 */
	synchronize_rcu();
}

static inline
bool ___urcu_grab_work(struct urcu_worker *worker,
		cds_wfcq_head_ptr_t src_head,
		struct cds_wfcq_tail *src_tail,
		bool steal)
{
	enum cds_wfcq_ret splice_ret;
	struct __cds_wfcq_head tmp_head;
	struct cds_wfcq_tail tmp_tail;
	struct cds_wfcq_node *node;

	/*
	 * Don't bother grabbing the src queue lock if it is empty.
	 */
	if (cds_wfcq_empty(src_head, src_tail))
		return false;
	__cds_wfcq_init(&tmp_head, &tmp_tail);

	/* Ensure that we preserve FIFO work order. */
	assert(!steal || worker->own == NULL);

	/* Splice to temporary queue. */
	if (steal)
		cds_wfcq_dequeue_lock(src_head.h, src_tail);
	splice_ret = __cds_wfcq_splice_blocking(&tmp_head,
			&tmp_tail,
			src_head,
			src_tail);
	if (steal)
		cds_wfcq_dequeue_unlock(src_head.h, src_tail);
	if (splice_ret == CDS_WFCQ_RET_SRC_EMPTY)
		return false;

	/*
	 * Keep one work entry for ourself. This ensures forward
	 * progress amongst stealing co-workers. This also ensures that
	 * when a worker grab some work from the global workqueue, it
	 * will have at least one work item to deal with.
	 */
	if (worker->own == NULL) {
		if (!steal) {
			/*
			 * Try to grab own work from worker workqueue to
			 * preserve FIFO order.
			 */
			node = cds_wfcq_dequeue_blocking(&worker->head,
				&worker->tail);
			if (node)
				goto got_node;
		}
		node = __cds_wfcq_dequeue_blocking(&tmp_head, &tmp_tail);
		assert(node != NULL);
got_node:
		worker->own = caa_container_of(node, struct urcu_work, node);
	}

	/* Splice into worker workqueue. */
	splice_ret = __cds_wfcq_splice_blocking(&worker->head,
			&worker->tail,
			&tmp_head,
			&tmp_tail);
	/* Ensure that we preserve FIFO work order. */
	assert(!steal || splice_ret != CDS_WFCQ_RET_DEST_NON_EMPTY);
	return true;
}

/*
 * Try stealing work from siblings when we have nothing to do.
 */
static inline
bool ___urcu_steal_work(struct urcu_worker *worker,
		struct urcu_worker *sibling)
{
	return ___urcu_grab_work(worker, &sibling->head, &sibling->tail, 1);
}

static inline
bool __urcu_steal_work(struct urcu_workqueue *queue,
		struct urcu_worker *worker)
{
	struct urcu_worker *sibling_prev, *sibling_next;
	struct cds_list_head *sibling_node;
	bool steal_performed = 0;

	if (!(worker->flags & URCU_WORKER_STEAL))
		return false;

	rcu_read_lock();

	sibling_node = rcu_dereference(worker->sibling_node.next);
	if (sibling_node == &queue->sibling_head)
		sibling_node = rcu_dereference(sibling_node->next);
	sibling_next = caa_container_of(sibling_node, struct urcu_worker,
			sibling_node);
	if (sibling_next != worker)
		steal_performed = ___urcu_steal_work(worker, sibling_next);
	if (steal_performed)
		goto end;

	sibling_node = rcu_dereference(worker->sibling_node.prev);
	if (sibling_node == &queue->sibling_head)
		sibling_node = rcu_dereference(sibling_node->prev);
	sibling_prev = caa_container_of(sibling_node, struct urcu_worker,
			sibling_node);
	if (sibling_prev != worker && sibling_prev != sibling_next)
		steal_performed =  ___urcu_steal_work(worker, sibling_prev);
end:
	rcu_read_unlock();

	return steal_performed;
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
enum urcu_accept_ret urcu_accept_work(struct urcu_worker *worker)
{
	struct urcu_workqueue *queue = worker->queue;
	enum cds_wfcq_ret wfcq_ret;
	bool has_work;

	has_work = ___urcu_grab_work(worker, &queue->head, &queue->tail, 0);
	/* Don't wait if we have work to do. */
	if (has_work || worker->own
			|| !cds_wfcq_empty(&worker->head, &worker->tail))
		goto do_work;
	/* Try to steal work from sibling instead of blocking */
	if (__urcu_steal_work(queue, worker))
		goto do_work;
	/* No more work to do, check shutdown state */
	if (CMM_LOAD_SHARED(queue->shutdown))
		return URCU_ACCEPT_SHUTDOWN;
	urcu_wait_set_state(&worker->wait_node,
			URCU_WAIT_WAITING);
	if (!CMM_LOAD_SHARED(worker->wait_node.node.next)) {
		int was_empty;

		/*
		 * NULL next pointer. We are therefore not in
		 * the queue.
		 */
		cds_lfs_node_init(&worker->wait_node.node);
		/* Protect stack dequeue against ABA */
		synchronize_rcu();
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
						&queue->tail)) {
			rcu_read_lock();	/* Protect stack dequeue */
			(void) urcu_dequeue_wake_single(&queue->waitqueue);
			rcu_read_unlock();	/* Protect stack dequeue */
		}
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
	return URCU_ACCEPT_WORK;
}

static inline
struct urcu_work *urcu_dequeue_work(struct urcu_worker *worker)
{
	struct urcu_workqueue *queue = worker->queue;
	struct cds_wfcq_node *node;
	struct urcu_work *work;

	if (worker->own) {
		/* Process our own work entry. */
		work = worker->own;
		worker->own = NULL;
		goto end;
	}
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
	work = caa_container_of(node, struct urcu_work, node);
end:
	if (queue->nr_work_max)
		uatomic_dec(&queue->nr_work);
	return work;
}

static inline
void urcu_workqueue_shutdown(struct urcu_workqueue *queue)
{
	/* Set shutdown */
	CMM_STORE_SHARED(queue->shutdown, true);
	/* Wakeup all workers */
	__urcu_workqueue_wakeup_all(queue);
}

/*
 * Use to let dispatcher steal work from the entire queue in case of
 * stall. The "worker" parameter need to be intialized, but is usually
 * not registered.
 */
static inline
bool urcu_workqueue_steal_all(struct urcu_workqueue *queue,
		struct urcu_worker *worker)
{
	struct urcu_worker *sibling;
	bool has_work = false;

	if (worker->flags & URCU_WORKER_STEAL) {
		rcu_read_lock();
		/* Steal from each worker */
		cds_list_for_each_entry_rcu(sibling, &queue->sibling_head,
				sibling_node)
			has_work |= ___urcu_grab_work(worker, &sibling->head,
						&sibling->tail, 1);
		rcu_read_unlock();
	}

	/* Steal from global workqueue */
	has_work |= ___urcu_grab_work(worker, &queue->head, &queue->tail, 0);
	return has_work;
}

#endif /* _URCU_WORKQUEUE_FIFO_H */
