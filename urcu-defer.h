#ifndef _URCU_BATCH_H
#define _URCU_BATCH_H

/*
 * urcu-defer.h
 *
 * Userspace RCU header - deferred execution
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 *
 * LGPL-compatible code should include this header with :
 *
 * #define _LGPL_SOURCE
 * #include <urcu-defer.h>
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

#include <stdlib.h>
#include <pthread.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Note: the defer_rcu() API is currently EXPERIMENTAL. It may change in the
 * future.
 * 
 * Important !
 *
 * Each thread queuing memory reclamation must be registered with
 * rcu_defer_register_thread(). rcu_defer_unregister_thread() should be
 * called before the thread exits.
 *
 * *NEVER* use defer_rcu() within a RCU read-side critical section, because this
 * primitive need to call synchronize_rcu() if the thread queue is full.
 */

extern void defer_rcu(void (*fct)(void *p), void *p);

/*
 * call_rcu will eventually be implemented with an API similar to the Linux
 * kernel call_rcu(), which will allow its use within RCU read-side C.S.
 * Generate an error if used for now.
 */

#define call_rcu	__error_call_rcu_not_implemented_please_use_defer_rcu

/*
 * Thread registration for reclamation.
 */
extern void rcu_defer_register_thread(void);
extern void rcu_defer_unregister_thread(void);
extern void rcu_defer_barrier(void);
extern void rcu_defer_barrier_thread(void);

#ifdef __cplusplus 
}
#endif

#endif /* _URCU_BATCH_H */
