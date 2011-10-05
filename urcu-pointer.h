#ifndef _URCU_POINTER_H
#define _URCU_POINTER_H

/*
 * urcu-pointer.h
 *
 * Userspace RCU header. Operations on pointers.
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

#include <urcu/compiler.h>
#include <urcu/arch.h>
#include <urcu/uatomic.h>

#ifdef __cplusplus
extern "C" {
#endif 

#ifdef _LGPL_SOURCE

#include <urcu/static/urcu-pointer.h>

/*
 * rcu_dereference(ptr)
 *
 * Fetch a RCU-protected pointer. Typically used to copy the variable ptr to a
 * local variable.
 */
#define rcu_dereference		_rcu_dereference

/*
 * rcu_cmpxchg_pointer(type **ptr, type *new, type *old)
 * type *rcu_xchg_pointer(type **ptr, type *new)
 * type *rcu_set_pointer(type **ptr, type *new)
 *
 * RCU pointer updates.
 * @ptr: address of the pointer to modify
 * @new: new pointer value
 * @old: old pointer value (expected)
 *
 * return: old pointer value
 */
#define rcu_cmpxchg_pointer	_rcu_cmpxchg_pointer
#define rcu_xchg_pointer	_rcu_xchg_pointer
#define rcu_set_pointer		_rcu_set_pointer

#else /* !_LGPL_SOURCE */

extern void *rcu_dereference_sym(void *p);
#define rcu_dereference(p)						     \
	({								     \
		typeof(p) _________p1 =	URCU_FORCE_CAST(typeof(p),	     \
			rcu_dereference_sym(URCU_FORCE_CAST(void *, p)));    \
		(_________p1);						     \
	})

extern void *rcu_cmpxchg_pointer_sym(void **p, void *old, void *_new);
#define rcu_cmpxchg_pointer(p, old, _new)				     \
	({								     \
		typeof(*(p)) _________pold = (old);			     \
		typeof(*(p)) _________pnew = (_new);			     \
		typeof(*(p)) _________p1 = URCU_FORCE_CAST(typeof(*(p)),     \
			rcu_cmpxchg_pointer_sym(URCU_FORCE_CAST(void **, p),\
						_________pold,		     \
						_________pnew));	     \
		(_________p1);						     \
	})

extern void *rcu_xchg_pointer_sym(void **p, void *v);
#define rcu_xchg_pointer(p, v)						     \
	({								     \
		typeof(*(p)) _________pv = (v);			             \
		typeof(*(p)) _________p1 = URCU_FORCE_CAST(typeof(*(p)),     \
			rcu_xchg_pointer_sym(URCU_FORCE_CAST(void **, p),    \
					     _________pv));		     \
		(_________p1);						     \
	})

extern void *rcu_set_pointer_sym(void **p, void *v);
#define rcu_set_pointer(p, v)						     \
	({								     \
		typeof(*(p)) _________pv = (v);			             \
		typeof(*(p)) _________p1 = URCU_FORCE_CAST(typeof(*(p)),     \
			rcu_set_pointer_sym(URCU_FORCE_CAST(void **, p),     \
					    _________pv));		     \
		(_________p1);						     \
	})

#endif /* !_LGPL_SOURCE */

/*
 * rcu_assign_pointer(type *ptr, type *new)
 *
 * Same as rcu_set_pointer, but takes the pointer to assign to rather than its
 * address as first parameter. Provided for compatibility with the Linux kernel
 * RCU semantic.
 */
#define rcu_assign_pointer(p, v)	rcu_set_pointer((&p), (v))

#ifdef __cplusplus 
}
#endif

#endif /* _URCU_POINTER_H */
