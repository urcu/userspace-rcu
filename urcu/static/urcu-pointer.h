#ifndef _URCU_POINTER_STATIC_H
#define _URCU_POINTER_STATIC_H

/*
 * urcu-pointer-static.h
 *
 * Userspace RCU header. Operations on pointers.
 *
 * TO BE INCLUDED ONLY IN LGPL-COMPATIBLE CODE. See urcu-pointer.h for
 * linking dynamically with the userspace rcu library.
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
#include <urcu/system.h>
#include <urcu/uatomic.h>

#ifdef __cplusplus
extern "C" {
#endif 

/**
 * _rcu_dereference - reads (copy) a RCU-protected pointer to a local variable
 * into a RCU read-side critical section. The pointer can later be safely
 * dereferenced within the critical section.
 *
 * This ensures that the pointer copy is invariant thorough the whole critical
 * section.
 *
 * Inserts memory barriers on architectures that require them (currently only
 * Alpha) and documents which pointers are protected by RCU.
 *
 * The compiler memory barrier in CMM_LOAD_SHARED() ensures that value-speculative
 * optimizations (e.g. VSS: Value Speculation Scheduling) does not perform the
 * data read before the pointer read by speculating the value of the pointer.
 * Correct ordering is ensured because the pointer is read as a volatile access.
 * This acts as a global side-effect operation, which forbids reordering of
 * dependent memory operations. Note that such concern about dependency-breaking
 * optimizations will eventually be taken care of by the "memory_order_consume"
 * addition to forthcoming C++ standard.
 *
 * Should match rcu_assign_pointer() or rcu_xchg_pointer().
 */

#define _rcu_dereference(p)     ({					\
				typeof(p) _________p1 = CMM_LOAD_SHARED(p); \
				cmm_smp_read_barrier_depends();		\
				(_________p1);				\
				})

/**
 * _rcu_cmpxchg_pointer - same as rcu_assign_pointer, but tests if the pointer
 * is as expected by "old". If succeeds, returns the previous pointer to the
 * data structure, which can be safely freed after waiting for a quiescent state
 * using synchronize_rcu(). If fails (unexpected value), returns old (which
 * should not be freed !).
 */

#define _rcu_cmpxchg_pointer(p, old, _new)				\
	({								\
		typeof(*p) _________pold = (old);			\
		typeof(*p) _________pnew = (_new);			\
		if (!__builtin_constant_p(_new) ||			\
		    ((_new) != NULL))					\
			cmm_wmb();						\
		uatomic_cmpxchg(p, _________pold, _________pnew);	\
	})

/**
 * _rcu_xchg_pointer - same as rcu_assign_pointer, but returns the previous
 * pointer to the data structure, which can be safely freed after waiting for a
 * quiescent state using synchronize_rcu().
 */

#define _rcu_xchg_pointer(p, v)				\
	({						\
		typeof(*p) _________pv = (v);		\
		if (!__builtin_constant_p(v) ||		\
		    ((v) != NULL))			\
			cmm_wmb();				\
		uatomic_xchg(p, _________pv);		\
	})


#define _rcu_set_pointer(p, v)				\
	({						\
		typeof(*p) _________pv = (v);		\
		if (!__builtin_constant_p(v) || 	\
		    ((v) != NULL))			\
			cmm_wmb();				\
		uatomic_set(p, _________pv);		\
	})

/**
 * _rcu_assign_pointer - assign (publicize) a pointer to a new data structure
 * meant to be read by RCU read-side critical sections. Returns the assigned
 * value.
 *
 * Documents which pointers will be dereferenced by RCU read-side critical
 * sections and adds the required memory barriers on architectures requiring
 * them. It also makes sure the compiler does not reorder code initializing the
 * data structure before its publication.
 *
 * Should match rcu_dereference_pointer().
 */

#define _rcu_assign_pointer(p, v)	_rcu_set_pointer(&(p), v)

#ifdef __cplusplus 
}
#endif

#endif /* _URCU_POINTER_STATIC_H */
