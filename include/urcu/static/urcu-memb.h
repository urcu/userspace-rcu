#ifndef _URCU_MEMB_STATIC_H
#define _URCU_MEMB_STATIC_H

/*
 * urcu-memb-static.h
 *
 * Userspace RCU header.
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
#include <unistd.h>
#include <stdint.h>

#include <urcu/config.h>
#include <urcu/compiler.h>
#include <urcu/arch.h>
#include <urcu/system.h>
#include <urcu/uatomic.h>
#include <urcu/list.h>
#include <urcu/futex.h>
#include <urcu/tls-compat.h>
#include <urcu/debug.h>
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

/*
 * Slave barriers are only guaranteed to be ordered wrt master barriers.
 *
 * The pair ordering is detailed as (O: ordered, X: not ordered) :
 *               slave  master
 *        slave    X      O
 *        master   O      O
 */

#ifdef CONFIG_RCU_FORCE_SYS_MEMBARRIER
#define urcu_memb_has_sys_membarrier		1
#else
extern int urcu_memb_has_sys_membarrier;
#endif

static inline void urcu_memb_smp_mb_slave(void)
{
	if (caa_likely(urcu_memb_has_sys_membarrier))
		cmm_barrier();
	else
		cmm_smp_mb();
}

extern struct urcu_gp urcu_memb_gp;

extern DECLARE_URCU_TLS(struct urcu_reader, urcu_memb_reader);

/*
 * Helper for _rcu_read_lock().  The format of urcu_memb_gp.ctr (as well as
 * the per-thread rcu_reader.ctr) has the upper bits containing a count of
 * _rcu_read_lock() nesting, and a lower-order bit that contains either zero
 * or URCU_GP_CTR_PHASE.  The smp_mb_slave() ensures that the accesses in
 * _rcu_read_lock() happen before the subsequent read-side critical section.
 */
static inline void _urcu_memb_read_lock_update(unsigned long tmp)
{
	if (caa_likely(!(tmp & URCU_GP_CTR_NEST_MASK))) {
		_CMM_STORE_SHARED(URCU_TLS(urcu_memb_reader).ctr, _CMM_LOAD_SHARED(urcu_memb_gp.ctr));
		urcu_memb_smp_mb_slave();
	} else
		_CMM_STORE_SHARED(URCU_TLS(urcu_memb_reader).ctr, tmp + URCU_GP_COUNT);
}

/*
 * Enter an RCU read-side critical section.
 *
 * The first cmm_barrier() call ensures that the compiler does not reorder
 * the body of _rcu_read_lock() with a mutex.
 *
 * This function and its helper are both less than 10 lines long.  The
 * intent is that this function meets the 10-line criterion in LGPL,
 * allowing this function to be invoked directly from non-LGPL code.
 */
static inline void _urcu_memb_read_lock(void)
{
	unsigned long tmp;

	urcu_assert(URCU_TLS(urcu_memb_reader).registered);
	cmm_barrier();
	tmp = URCU_TLS(urcu_memb_reader).ctr;
	urcu_assert((tmp & URCU_GP_CTR_NEST_MASK) != URCU_GP_CTR_NEST_MASK);
	_urcu_memb_read_lock_update(tmp);
}

/*
 * This is a helper function for _rcu_read_unlock().
 *
 * The first smp_mb_slave() call ensures that the critical section is
 * seen to precede the store to rcu_reader.ctr.
 * The second smp_mb_slave() call ensures that we write to rcu_reader.ctr
 * before reading the update-side futex.
 */
static inline void _urcu_memb_read_unlock_update_and_wakeup(unsigned long tmp)
{
	if (caa_likely((tmp & URCU_GP_CTR_NEST_MASK) == URCU_GP_COUNT)) {
		urcu_memb_smp_mb_slave();
		_CMM_STORE_SHARED(URCU_TLS(urcu_memb_reader).ctr, tmp - URCU_GP_COUNT);
		urcu_memb_smp_mb_slave();
		urcu_common_wake_up_gp(&urcu_memb_gp);
	} else
		_CMM_STORE_SHARED(URCU_TLS(urcu_memb_reader).ctr, tmp - URCU_GP_COUNT);
}

/*
 * Exit an RCU read-side crtical section.  Both this function and its
 * helper are smaller than 10 lines of code, and are intended to be
 * usable by non-LGPL code, as called out in LGPL.
 */
static inline void _urcu_memb_read_unlock(void)
{
	unsigned long tmp;

	urcu_assert(URCU_TLS(urcu_memb_reader).registered);
	tmp = URCU_TLS(urcu_memb_reader).ctr;
	urcu_assert(tmp & URCU_GP_CTR_NEST_MASK);
	_urcu_memb_read_unlock_update_and_wakeup(tmp);
	cmm_barrier();	/* Ensure the compiler does not reorder us with mutex */
}

/*
 * Returns whether within a RCU read-side critical section.
 *
 * This function is less than 10 lines long.  The intent is that this
 * function meets the 10-line criterion for LGPL, allowing this function
 * to be invoked directly from non-LGPL code.
 */
static inline int _urcu_memb_read_ongoing(void)
{
	return URCU_TLS(urcu_memb_reader).ctr & URCU_GP_CTR_NEST_MASK;
}

#ifdef __cplusplus
}
#endif

#endif /* _URCU_MEMB_STATIC_H */
