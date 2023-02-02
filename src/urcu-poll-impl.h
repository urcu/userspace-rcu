/*
 * urcu-poll-impl.h
 *
 * Userspace RCU library - Grace period polling API
 *
 * Copyright (c) 2023 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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
#include <stdbool.h>

#include <urcu/urcu-poll.h>
#include <urcu/call-rcu.h>

struct urcu_poll_worker_state {
	struct urcu_gp_poll_state current_state;
	struct urcu_gp_poll_state latest_target;	/* Most recent snapshot taken */
	struct rcu_head rcu_head;
	pthread_mutex_t lock;
	bool active;
};

static struct urcu_poll_worker_state poll_worker_gp_state = {
	.lock = PTHREAD_MUTEX_INITIALIZER,
};

static
void urcu_poll_worker_cb(struct rcu_head *head __attribute__((unused)))
{
	mutex_lock(&poll_worker_gp_state.lock);
	/* A new grace period has been reached. */
	poll_worker_gp_state.current_state.grace_period_id++;
	if ((long)(poll_worker_gp_state.latest_target.grace_period_id - poll_worker_gp_state.current_state.grace_period_id) >= 0) {
		/* Need to re-queue. */
		call_rcu(&poll_worker_gp_state.rcu_head, urcu_poll_worker_cb);
	} else {
		/* No user waiting for a target grace period. */
		poll_worker_gp_state.active = false;
	}
	mutex_unlock(&poll_worker_gp_state.lock);
}

/*
 * Start polling on grace period. If no worker is currently active,
 * snapshot the current value and start a worker callback. If the worker
 * is currently active, snapshot the current value + 1, and set this
 * value as the latest snapshot, which will cause the worker to re-queue
 * itself with call_rcu to issue one more grace period.
 *
 * Because it uses call_rcu, it needs to be called from a registered RCU
 * thread.
 */
struct urcu_gp_poll_state start_poll_synchronize_rcu(void)
{
	struct urcu_gp_poll_state new_target_gp_state;
	bool was_active = false;

	mutex_lock(&poll_worker_gp_state.lock);
	new_target_gp_state.grace_period_id = poll_worker_gp_state.current_state.grace_period_id;
	was_active = poll_worker_gp_state.active;
	if (!was_active)
		poll_worker_gp_state.active = true;
	else
		new_target_gp_state.grace_period_id++;
	poll_worker_gp_state.latest_target.grace_period_id = new_target_gp_state.grace_period_id;
	if (!was_active)
		call_rcu(&poll_worker_gp_state.rcu_head, urcu_poll_worker_cb);
	mutex_unlock(&poll_worker_gp_state.lock);
	return new_target_gp_state;
}

/*
 * Poll the grace period state. Return true if quiescence was reached
 * since the snapshot was taken, return false if quiescence was not
 * reached since snapshot.
 */
bool poll_state_synchronize_rcu(struct urcu_gp_poll_state target_gp_state)
{
	bool target_gp_reached = false;

	mutex_lock(&poll_worker_gp_state.lock);
	if ((long)(target_gp_state.grace_period_id - poll_worker_gp_state.current_state.grace_period_id) < 0)
		target_gp_reached = true;
	mutex_unlock(&poll_worker_gp_state.lock);
	return target_gp_reached;
}
