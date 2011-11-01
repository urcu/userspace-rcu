#ifndef _URCU_COMPILER_H
#define _URCU_COMPILER_H

/*
 * compiler.h
 *
 * Compiler definitions.
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 *
 * THIS MATERIAL IS PROVIDED AS IS, WITH ABSOLUTELY NO WARRANTY EXPRESSED
 * OR IMPLIED.  ANY USE IS AT YOUR OWN RISK.
 *
 * Permission is hereby granted to use or copy this program
 * for any purpose,  provided the above notices are retained on all copies.
 * Permission to modify the code and to distribute modified code is granted,
 * provided the above notices are retained, and a notice that the code was
 * modified is included with the above copyright notice.
 */

#include <stddef.h>	/* for offsetof */

#define caa_likely(x)	__builtin_expect(!!(x), 1)
#define caa_unlikely(x)	__builtin_expect(!!(x), 0)

#define	cmm_barrier()	asm volatile("" : : : "memory")

/*
 * Instruct the compiler to perform only a single access to a variable
 * (prohibits merging and refetching). The compiler is also forbidden to reorder
 * successive instances of CMM_ACCESS_ONCE(), but only when the compiler is aware of
 * particular ordering. Compiler ordering can be ensured, for example, by
 * putting two CMM_ACCESS_ONCE() in separate C statements.
 *
 * This macro does absolutely -nothing- to prevent the CPU from reordering,
 * merging, or refetching absolutely anything at any time.  Its main intended
 * use is to mediate communication between process-level code and irq/NMI
 * handlers, all running on the same CPU.
 */
#define CMM_ACCESS_ONCE(x)	(*(volatile typeof(x) *)&(x))

#ifndef caa_max
#define caa_max(a,b) ((a)>(b)?(a):(b))
#endif

#ifndef caa_min
#define caa_min(a,b) ((a)<(b)?(a):(b))
#endif

#if defined(__SIZEOF_LONG__)
#define CAA_BITS_PER_LONG	(__SIZEOF_LONG__ * 8)
#elif defined(_LP64)
#define CAA_BITS_PER_LONG	64
#else
#define CAA_BITS_PER_LONG	32
#endif

/*
 * caa_container_of - Get the address of an object containing a field.
 *
 * @ptr: pointer to the field.
 * @type: type of the object.
 * @member: name of the field within the object.
 */
#define caa_container_of(ptr, type, member)				\
	({								\
		const typeof(((type *) NULL)->member) * __ptr = (ptr);	\
		(type *)((char *)__ptr - offsetof(type, member));	\
	})

#define CAA_BUILD_BUG_ON_ZERO(cond) (sizeof(struct { int:-!!(cond); }))
#define CAA_BUILD_BUG_ON(cond) ((void)BUILD_BUG_ON_ZERO(cond))

/*
 * __rcu is an annotation that documents RCU pointer accesses that need
 * to be protected by a read-side critical section. Eventually, a static
 * checker will be able to use this annotation to detect incorrect RCU
 * usage.
 */
#define __rcu

#ifdef __cplusplus
#define URCU_FORCE_CAST(type, arg)	(reinterpret_cast<type>(arg))
#else
#define URCU_FORCE_CAST(type, arg)	((type) (arg))
#endif

#endif /* _URCU_COMPILER_H */
