#ifndef _URCU_QSBR_STATIC_H
#define _URCU_QSBR_STATIC_H

/*
 * urcu-qsbr-static.h
 *
 * Userspace RCU QSBR header.
 *
 * TO BE INCLUDED ONLY IN CODE THAT IS TO BE RECOMPILED ON EACH LIBURCU
 * RELEASE. See urcu.h for linking dynamically with the userspace rcu library.
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
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
 *
 * IBM's contributions to this file may be relicensed under LGPLv2 or later.
 */

#include <stdlib.h>
#include <pthread.h>
#include <limits.h>
#include <unistd.h>
#include <stdint.h>

#include <urcu/debug.h>
#include <urcu/compiler.h>
#include <urcu/arch.h>
#include <urcu/system.h>
#include <urcu/uatomic.h>
#include <urcu/list.h>
#include <urcu/futex.h>
#include <urcu/tls-compat.h>
#include <urcu/static/urcu-common.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * This code section can only be included in LGPL 2.1 compatible source code.
 * See below for the function call wrappers which can be used in code meant to
 * be only linked with the Userspace RCU library. This comes with a small
 * performance degradation on the read-side due to the added function calls.
 * This is required to permit relinking with newer versions of the library.
 */

#define URCU_QSBR_GP_ONLINE		(1UL << 0)
#define URCU_QSBR_GP_CTR		(1UL << 1)

extern struct urcu_gp urcu_qsbr_gp;

struct urcu_qsbr_reader {
	/* Data used by both reader and synchronize_rcu() */
	unsigned long ctr;
	/* Data used for registry */
	struct cds_list_head node __attribute__((aligned(CAA_CACHE_LINE_SIZE)));
	int waiting;
	pthread_t tid;
	/* Reader registered flag, for internal checks. */
	unsigned int registered:1;
};

extern DECLARE_URCU_TLS(struct urcu_qsbr_reader, urcu_qsbr_reader);

/*
 * Wake-up waiting synchronize_rcu(). Called from many concurrent threads.
 */
static inline void urcu_qsbr_wake_up_gp(void)
{
	if (caa_unlikely(_CMM_LOAD_SHARED(URCU_TLS(urcu_qsbr_reader).waiting))) {
		_CMM_STORE_SHARED(URCU_TLS(urcu_qsbr_reader).waiting, 0);
		cmm_smp_mb();
		if (uatomic_read(&urcu_qsbr_gp.futex) != -1)
			return;
		uatomic_set(&urcu_qsbr_gp.futex, 0);
		/*
		 * Ignoring return value until we can make this function
		 * return something (because urcu_die() is not publicly
		 * exposed).
		 */
		(void) futex_noasync(&urcu_qsbr_gp.futex, FUTEX_WAKE, 1,
				NULL, NULL, 0);
	}
}

static inline enum urcu_state urcu_qsbr_reader_state(unsigned long *ctr)
{
	unsigned long v;

	v = CMM_LOAD_SHARED(*ctr);
	if (!v)
		return URCU_READER_INACTIVE;
	if (v == urcu_qsbr_gp.ctr)
		return URCU_READER_ACTIVE_CURRENT;
	return URCU_READER_ACTIVE_OLD;
}

/*
 * Enter an RCU read-side critical section.
 *
 * This function is less than 10 lines long.  The intent is that this
 * function meets the 10-line criterion for LGPL, allowing this function
 * to be invoked directly from non-LGPL code.
 */
static inline void _urcu_qsbr_read_lock(void)
{
	urcu_assert_debug(URCU_TLS(urcu_qsbr_reader).ctr);
}

/*
 * Exit an RCU read-side critical section.
 *
 * This function is less than 10 lines long.  The intent is that this
 * function meets the 10-line criterion for LGPL, allowing this function
 * to be invoked directly from non-LGPL code.
 */
static inline void _urcu_qsbr_read_unlock(void)
{
	urcu_assert_debug(URCU_TLS(urcu_qsbr_reader).ctr);
}

/*
 * Returns whether within a RCU read-side critical section.
 *
 * This function is less than 10 lines long.  The intent is that this
 * function meets the 10-line criterion for LGPL, allowing this function
 * to be invoked directly from non-LGPL code.
 */
static inline int _urcu_qsbr_read_ongoing(void)
{
	return URCU_TLS(urcu_qsbr_reader).ctr;
}

/*
 * This is a helper function for _rcu_quiescent_state().
 * The first cmm_smp_mb() ensures memory accesses in the prior read-side
 * critical sections are not reordered with store to
 * URCU_TLS(urcu_qsbr_reader).ctr, and ensures that mutexes held within an
 * offline section that would happen to end with this
 * urcu_qsbr_quiescent_state() call are not reordered with
 * store to URCU_TLS(urcu_qsbr_reader).ctr.
 */
static inline void _urcu_qsbr_quiescent_state_update_and_wakeup(unsigned long gp_ctr)
{
	cmm_smp_mb();
	_CMM_STORE_SHARED(URCU_TLS(urcu_qsbr_reader).ctr, gp_ctr);
	cmm_smp_mb();	/* write URCU_TLS(urcu_qsbr_reader).ctr before read futex */
	urcu_qsbr_wake_up_gp();
	cmm_smp_mb();
}

/*
 * Inform RCU of a quiescent state.
 *
 * This function is less than 10 lines long.  The intent is that this
 * function meets the 10-line criterion for LGPL, allowing this function
 * to be invoked directly from non-LGPL code.
 *
 * We skip the memory barriers and gp store if our local ctr already
 * matches the global urcu_qsbr_gp.ctr value: this is OK because a prior
 * _rcu_quiescent_state() or _rcu_thread_online() already updated it
 * within our thread, so we have no quiescent state to report.
 */
static inline void _urcu_qsbr_quiescent_state(void)
{
	unsigned long gp_ctr;

	urcu_assert_debug(URCU_TLS(urcu_qsbr_reader).registered);
	if ((gp_ctr = CMM_LOAD_SHARED(urcu_qsbr_gp.ctr)) == URCU_TLS(urcu_qsbr_reader).ctr)
		return;
	_urcu_qsbr_quiescent_state_update_and_wakeup(gp_ctr);
}

/*
 * Take a thread offline, prohibiting it from entering further RCU
 * read-side critical sections.
 *
 * This function is less than 10 lines long.  The intent is that this
 * function meets the 10-line criterion for LGPL, allowing this function
 * to be invoked directly from non-LGPL code.
 */
static inline void _urcu_qsbr_thread_offline(void)
{
	urcu_assert_debug(URCU_TLS(urcu_qsbr_reader).registered);
	cmm_smp_mb();
	CMM_STORE_SHARED(URCU_TLS(urcu_qsbr_reader).ctr, 0);
	cmm_smp_mb();	/* write URCU_TLS(urcu_qsbr_reader).ctr before read futex */
	urcu_qsbr_wake_up_gp();
	cmm_barrier();	/* Ensure the compiler does not reorder us with mutex */
}

/*
 * Bring a thread online, allowing it to once again enter RCU
 * read-side critical sections.
 *
 * This function is less than 10 lines long.  The intent is that this
 * function meets the 10-line criterion for LGPL, allowing this function
 * to be invoked directly from non-LGPL code.
 */
static inline void _urcu_qsbr_thread_online(void)
{
	urcu_assert_debug(URCU_TLS(urcu_qsbr_reader).registered);
	cmm_barrier();	/* Ensure the compiler does not reorder us with mutex */
	_CMM_STORE_SHARED(URCU_TLS(urcu_qsbr_reader).ctr, CMM_LOAD_SHARED(urcu_qsbr_gp.ctr));
	cmm_smp_mb();
}

#ifdef __cplusplus
}
#endif

#endif /* _URCU_QSBR_STATIC_H */
