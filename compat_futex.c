/*
 * compat_futex.c
 *
 * Userspace RCU library - sys_futex compatibility code
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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

#include <stdio.h>
#include <pthread.h>
#include <signal.h>
#include <assert.h>
#include <errno.h>
#include <poll.h>
#include <stdint.h>

#include <urcu/arch.h>
#include <urcu/futex.h>

static pthread_mutex_t compat_futex_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t compat_futex_cond = PTHREAD_COND_INITIALIZER;

/*
 * _NOT SIGNAL-SAFE_. pthread_cond is not signal-safe anyway. Though.
 * For now, timeout, uaddr2 and val3 are unused.
 * Waiter will relinquish the CPU until woken up.
 */

int compat_futex_noasync(int32_t *uaddr, int op, int32_t val,
	const struct timespec *timeout, int32_t *uaddr2, int32_t val3)
{
	int ret, i, gret = 0;

	/*
	 * Check if NULL. Don't let users expect that they are taken into
	 * account. 
	 */
	assert(!timeout);
	assert(!uaddr2);
	assert(!val3);

	/*
	 * memory barriers to serialize with the previous uaddr modification.
	 */
	cmm_smp_mb();

	ret = pthread_mutex_lock(&compat_futex_lock);
	assert(!ret);
	switch (op) {
	case FUTEX_WAIT:
		if (*uaddr != val)
			goto end;
		pthread_cond_wait(&compat_futex_cond, &compat_futex_lock);
		break;
	case FUTEX_WAKE:
		for (i = 0; i < val; i++)
			pthread_cond_signal(&compat_futex_cond);
		break;
	default:
		gret = -EINVAL;
	}
end:
	ret = pthread_mutex_unlock(&compat_futex_lock);
	assert(!ret);
	return gret;
}

/*
 * _ASYNC SIGNAL-SAFE_.
 * For now, timeout, uaddr2 and val3 are unused.
 * Waiter will busy-loop trying to read the condition.
 */

int compat_futex_async(int32_t *uaddr, int op, int32_t val,
	const struct timespec *timeout, int32_t *uaddr2, int32_t val3)
{
	/*
	 * Check if NULL. Don't let users expect that they are taken into
	 * account. 
	 */
	assert(!timeout);
	assert(!uaddr2);
	assert(!val3);

	/*
	 * Ensure previous memory operations on uaddr have completed.
	 */
	cmm_smp_mb();

	switch (op) {
	case FUTEX_WAIT:
		while (*uaddr == val)
			poll(NULL, 0, 10);
		break;
	case FUTEX_WAKE:
		break;
	default:
		return -EINVAL;
	}
	return 0;
}
