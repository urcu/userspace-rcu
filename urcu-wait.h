#ifndef _URCU_WAIT_H
#define _URCU_WAIT_H

/*
 * urcu-wait.h
 *
 * Userspace RCU library wait/wakeup management
 *
 * Copyright (c) 2012 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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

/*
 * Number of busy-loop attempts before waiting on futex for grace period
 * batching.
 */
#define URCU_WAIT_ATTEMPTS 1000

enum urcu_wait_state {
	/* URCU_WAIT_WAITING is compared directly (futex compares it). */
	URCU_WAIT_WAITING =	0,
	/* non-zero are used as masks. */
	URCU_WAIT_WAKEUP =	(1 << 0),
	URCU_WAIT_AWAKENED =	(1 << 1),
	URCU_WAIT_TEARDOWN =	(1 << 2),
};

struct urcu_wait {
	int32_t futex;
};

static inline
void urcu_wait_init(struct urcu_wait *wait)
{
	wait->futex = URCU_WAIT_WAITING;
}

/*
 * Note: urcu_adaptative_wake_up needs "value" to stay allocated
 * throughout its execution. In this scheme, the waiter owns the futex
 * memory, and we only allow it to free this memory when it receives the
 * URCU_WAIT_TEARDOWN flag.
 */
static inline
void urcu_adaptative_wake_up(struct urcu_wait *wait)
{
	cmm_smp_mb();
	assert(uatomic_read(&wait->futex) == URCU_WAIT_WAITING);
	uatomic_set(&wait->futex, URCU_WAIT_WAKEUP);
	if (!(uatomic_read(&wait->futex) & URCU_WAIT_AWAKENED))
		futex_noasync(&wait->futex, FUTEX_WAKE, 1, NULL, NULL, 0);
	/* Allow teardown of struct urcu_wait memory. */
	uatomic_or(&wait->futex, URCU_WAIT_TEARDOWN);
}

/*
 * Caller must initialize "value" to URCU_WAIT_WAITING before passing its
 * memory to waker thread.
 */
static void urcu_adaptative_busy_wait(struct urcu_wait *wait)
{
	unsigned int i;

	/* Load and test condition before read futex */
	cmm_smp_rmb();
	for (i = 0; i < URCU_WAIT_ATTEMPTS; i++) {
		if (uatomic_read(&wait->futex) != URCU_WAIT_WAITING)
			goto skip_futex_wait;
		caa_cpu_relax();
	}
	futex_noasync(&wait->futex, FUTEX_WAIT,
		URCU_WAIT_WAITING, NULL, NULL, 0);
skip_futex_wait:

	/* Tell waker thread than we are awakened. */
	uatomic_or(&wait->futex, URCU_WAIT_AWAKENED);

	/*
	 * Wait until waker thread lets us know it's ok to tear down
	 * memory allocated for struct urcu_wait.
	 */
	for (i = 0; i < URCU_WAIT_ATTEMPTS; i++) {
		if (uatomic_read(&wait->futex) & URCU_WAIT_TEARDOWN)
			break;
		caa_cpu_relax();
	}
	while (!(uatomic_read(&wait->futex) & URCU_WAIT_TEARDOWN))
		poll(NULL, 0, 10);
	assert(uatomic_read(&wait->futex) & URCU_WAIT_TEARDOWN);
}

#endif /* _URCU_WAIT_H */
