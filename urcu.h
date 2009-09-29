#ifndef _URCU_H
#define _URCU_H

/*
 * urcu.h
 *
 * Userspace RCU header
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
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

/*
 * Important !
 *
 * Each thread containing read-side critical sections must be registered
 * with rcu_register_thread() before calling rcu_read_lock().
 * rcu_unregister_thread() should be called before the thread exits.
 */

#ifdef _LGPL_SOURCE

#include <urcu-static.h>

/*
 * Mappings for static use of the userspace RCU library.
 * Should only be used in LGPL-compatible code.
 */

#define rcu_dereference		_rcu_dereference
#define rcu_read_lock		_rcu_read_lock
#define rcu_read_unlock		_rcu_read_unlock

#define rcu_assign_pointer	_rcu_assign_pointer
#define rcu_cmpxchg_pointer	_rcu_cmpxchg_pointer
#define rcu_xchg_pointer	_rcu_xchg_pointer
#define rcu_publish_content	_rcu_publish_content

#else /* !_LGPL_SOURCE */

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

extern void rcu_read_lock(void);
extern void rcu_read_unlock(void);

extern void *rcu_dereference(void *p);

extern void *rcu_assign_pointer_sym(void **p, void *v);

#define rcu_assign_pointer(p, v)			\
	rcu_assign_pointer_sym((void **)(p), (v))

extern void *rcu_cmpxchg_pointer_sym(void **p, void *old, void *_new);
#define rcu_cmpxchg_pointer(p, old, _new)		\
	rcu_cmpxchg_pointer_sym((void **)(p), (old), (_new))

extern void *rcu_xchg_pointer_sym(void **p, void *v);
#define rcu_xchg_pointer(p, v)				\
	rcu_xchg_pointer_sym((void **)(p), (v))

extern void *rcu_publish_content_sym(void **p, void *v);
#define rcu_publish_content(p, v)			\
	rcu_publish_content_sym((void **)(p), (v))

#endif /* !_LGPL_SOURCE */

extern void synchronize_rcu(void);

/*
 * Reader thread registration.
 */
extern void rcu_register_thread(void);
extern void rcu_unregister_thread(void);

/*
 * Explicit urcu initialization, for "early" use within library constructors.
 */
extern void urcu_init(void);

#endif /* _URCU_H */
