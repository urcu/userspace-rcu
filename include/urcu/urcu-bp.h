#ifndef _URCU_BP_H
#define _URCU_BP_H

/*
 * urcu-bp.h
 *
 * Userspace RCU header, "bulletproof" version.
 *
 * Slower RCU read-side adapted for tracing library. Does not require thread
 * registration nor unregistration. Also signal-safe.
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 *
 * LGPL-compatible code should include this header with :
 *
 * #define _LGPL_SOURCE
 * #include <urcu.h>
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

#include <urcu/map/urcu-bp.h>

/*
 * Important !
 *
 * Each thread containing read-side critical sections must be registered
 * with rcu_register_thread() before calling rcu_read_lock().
 * rcu_unregister_thread() should be called before the thread exits.
 */

/*
 * See urcu/pointer.h and urcu/static/pointer.h for pointer
 * publication headers.
 */
#include <urcu/pointer.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifdef _LGPL_SOURCE

#include <urcu/static/urcu-bp.h>

/*
 * Mappings for static use of the userspace RCU library.
 * Should only be used in LGPL-compatible code.
 */

/*
 * rcu_read_lock()
 * rcu_read_unlock()
 *
 * Mark the beginning and end of a read-side critical section.
 */
#define urcu_bp_read_lock		_urcu_bp_read_lock
#define urcu_bp_read_unlock		_urcu_bp_read_unlock
#define urcu_bp_read_ongoing		_urcu_bp_read_ongoing

#define urcu_bp_dereference		rcu_dereference
#define urcu_bp_cmpxchg_pointer		rcu_cmpxchg_pointer
#define urcu_bp_xchg_pointer		rcu_xchg_pointer
#define urcu_bp_set_pointer		rcu_set_pointer

#else /* !_LGPL_SOURCE */

/*
 * library wrappers to be used by non-LGPL compatible source code.
 * See LGPL-only urcu/static/pointer.h for documentation.
 */

extern void urcu_bp_read_lock(void);
extern void urcu_bp_read_unlock(void);
extern int urcu_bp_read_ongoing(void);

extern void *urcu_bp_dereference_sym(void *p);
#define urcu_bp_dereference(p)						     \
	__extension__							     \
	({								     \
		__typeof__(p) _________p1 = URCU_FORCE_CAST(__typeof__(p),   \
			urcu_bp_dereference_sym(URCU_FORCE_CAST(void *, p))); \
		(_________p1);						     \
	})

extern void *urcu_bp_cmpxchg_pointer_sym(void **p, void *old, void *_new);
#define urcu_bp_cmpxchg_pointer(p, old, _new)				     \
	__extension__							     \
	({								     \
		__typeof__(*(p)) _________pold = (old);			     \
		__typeof__(*(p)) _________pnew = (_new);		     \
		__typeof__(*(p)) _________p1 = URCU_FORCE_CAST(__typeof__(*(p)), \
			urcu_bp_cmpxchg_pointer_sym(URCU_FORCE_CAST(void **, p), \
						_________pold,		     \
						_________pnew));	     \
		(_________p1);						     \
	})

extern void *urcu_bp_xchg_pointer_sym(void **p, void *v);
#define urcu_bp_xchg_pointer(p, v)					     \
	__extension__							     \
	({								     \
		__typeof__(*(p)) _________pv = (v);			     \
		__typeof__(*(p)) _________p1 = URCU_FORCE_CAST(__typeof__(*(p)),\
			urcu_bp_xchg_pointer_sym(URCU_FORCE_CAST(void **, p), \
					     _________pv));		     \
		(_________p1);						     \
	})

extern void *urcu_bp_set_pointer_sym(void **p, void *v);
#define urcu_bp_set_pointer(p, v)					     \
	__extension__							     \
	({								     \
		__typeof__(*(p)) _________pv = (v);			     \
		__typeof__(*(p)) _________p1 = URCU_FORCE_CAST(__typeof__(*(p)), \
			urcu_bp_set_pointer_sym(URCU_FORCE_CAST(void **, p), \
					    _________pv));		     \
		(_________p1);						     \
	})

#endif /* !_LGPL_SOURCE */

extern void urcu_bp_synchronize_rcu(void);

/*
 * urcu_bp_before_fork, urcu_bp_after_fork_parent and urcu_bp_after_fork_child
 * should be called around fork() system calls when the child process is not
 * expected to immediately perform an exec(). For pthread users, see
 * pthread_atfork(3).
 */
extern void urcu_bp_before_fork(void);
extern void urcu_bp_after_fork_parent(void);
extern void urcu_bp_after_fork_child(void);

/*
 * In the bulletproof version, thread registration is performed lazily,
 * but it can be forced by issuing an explicit urcu_bp_register_thread().
 */
extern void urcu_bp_register_thread(void);

/*
 * In the bulletproof version, the following functions are no-ops.
 */
static inline void urcu_bp_unregister_thread(void)
{
}

static inline void urcu_bp_init(void)
{
}

/*
 * Q.S. reporting are no-ops for these URCU flavors.
 */
static inline void urcu_bp_quiescent_state(void)
{
}

static inline void urcu_bp_thread_offline(void)
{
}

static inline void urcu_bp_thread_online(void)
{
}

#ifdef __cplusplus
}
#endif

#include <urcu/call-rcu.h>
#include <urcu/defer.h>
#include <urcu/flavor.h>

#ifndef URCU_API_MAP
#include <urcu/map/clear.h>
#endif

#endif /* _URCU_BP_H */
