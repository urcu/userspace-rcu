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

#define likely(x)	__builtin_expect(!!(x), 1)
#define unlikely(x)	__builtin_expect(!!(x), 0)

#define	barrier()	asm volatile("" : : : "memory")

/*
 * Instruct the compiler to perform only a single access to a variable
 * (prohibits merging and refetching). The compiler is also forbidden to reorder
 * successive instances of ACCESS_ONCE(), but only when the compiler is aware of
 * particular ordering. Compiler ordering can be ensured, for example, by
 * putting two ACCESS_ONCE() in separate C statements.
 *
 * This macro does absolutely -nothing- to prevent the CPU from reordering,
 * merging, or refetching absolutely anything at any time.  Its main intended
 * use is to mediate communication between process-level code and irq/NMI
 * handlers, all running on the same CPU.
 */
#define ACCESS_ONCE(x)	(*(volatile typeof(x) *)&(x))

#ifndef max
#define max(a,b) ((a)>(b)?(a):(b))
#endif

#ifndef min
#define min(a,b) ((a)<(b)?(a):(b))
#endif

#if defined(__SIZEOF_LONG__)
#define BITS_PER_LONG	(__SIZEOF_LONG__ * 8)
#elif defined(_LP64)
#define BITS_PER_LONG	64
#else
#define BITS_PER_LONG	32
#endif

#endif /* _URCU_COMPILER_H */
