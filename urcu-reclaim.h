#ifndef _URCU_RECLAIM_H
#define _URCU_RECLAIM_H

/*
 * urcu-reclaim.h
 *
 * Userspace RCU header - memory reclamation
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 *
 * LGPL-compatible code should include this header with :
 *
 * #define _LGPL_SOURCE
 * #include <urcu-reclaim.h>
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

/*
 * Important !
 *
 * Each thread queuing memory reclamation must be registered with
 * rcu_reclaim_register_thread(). rcu_reclaim_unregister_thread() should be
 * called before the thread exits.
 */

#ifdef _LGPL_SOURCE

#include <urcu-reclaim-static.h>

/*
 * Mappings for static use of the userspace RCU library.
 * Should only be used in LGPL-compatible code.
 */

#define rcu_reclaim_queue	_rcu_reclaim_queue

#else /* !_LGPL_SOURCE */

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

extern void rcu_reclaim_queue(void *p);

#endif /* !_LGPL_SOURCE */

/*
 * Thread registration for reclamation.
 */
extern void rcu_reclaim_register_thread(void);
extern void rcu_reclaim_unregister_thread(void);
extern void rcu_reclaim_barrier(void);
extern void rcu_reclaim_barrier_thread(void);

#endif /* _URCU_RECLAIM_H */
