#ifndef _ARCH_PPC_H
#define _ARCH_PPC_H

/*
 * arch_ppc.h: trivial definitions for the powerpc architecture.
 *
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
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

#include <compiler.h>

#define CONFIG_HAVE_FENCE 1
#define CONFIG_HAVE_MEM_COHERENCY

#ifndef BITS_PER_LONG
#define BITS_PER_LONG   (sizeof(unsigned long) * 8)
#endif

#define mb()    asm volatile("sync":::"memory")
#define rmb()   asm volatile("sync":::"memory")
#define wmb()   asm volatile("sync"::: "memory")

/*
 * Architectures without cache coherency need something like the following:
 *
 * #define mb()		mc()
 * #define rmb()	rmc()
 * #define wmb()	wmc()
 * #define mc()		arch_cache_flush()
 * #define rmc()	arch_cache_flush_read()
 * #define wmc()	arch_cache_flush_write()
 */

#define mc()	barrier()
#define rmc()	barrier()
#define wmc()	barrier()

/* Assume SMP machine, given we don't have this information */
#define CONFIG_SMP 1

#ifdef CONFIG_SMP
#define smp_mb()	mb()
#define smp_rmb()	rmb()
#define smp_wmb()	wmb()
#define smp_mc()	mc()
#define smp_rmc()	rmc()
#define smp_wmc()	wmc()
#else
#define smp_mb()	barrier()
#define smp_rmb()	barrier()
#define smp_wmb()	barrier()
#define smp_mc()	barrier()
#define smp_rmc()	barrier()
#define smp_wmc()	barrier()
#endif

/* Nop everywhere except on alpha. */
#define smp_read_barrier_depends()

static inline void cpu_relax(void)
{
	barrier();
}

#define PPC405_ERR77(ra,rb)
#define LWSYNC_ON_SMP "\n\tlwsync\n"
#define ISYNC_ON_SMP "\n\tisync\n"

struct __xchg_dummy {
	unsigned long a[100];
};
#define __xg(x) ((struct __xchg_dummy *)(x))

#ifndef _INCLUDE_API_H

/*
 * Exchange the 32-bits value pointed to by p, returns the old value.
 * Might not work with PPC405 (see err 77).
 */
static __always_inline
unsigned int __xchg_u32(volatile void *p, unsigned int val)
{
	unsigned int prev;

	__asm__ __volatile__(LWSYNC_ON_SMP
		"1:\t"	     "lwarx	%0,0,%2\n"
			     "stwcx.	%3,0,%2\n"
			     "bne-	1b"
			     ISYNC_ON_SMP
			     : "=&r" (prev), "+m" (*(volatile unsigned int *)p)
			     : "r" (p), "r" (val)
			     : "cc", "memory");
	return prev;
}

#if (BITS_PER_LONG == 64)
/*
 * Exchange the 64-bits value pointed to by p, returns the old value.
 * Might not work with PPC405 (see err 77).
 */
static __always_inline
unsigned long __xchg_u64(volatile void *p, unsigned long val)
{
	unsigned long prev;

	__asm__ __volatile__(LWSYNC_ON_SMP
		"1:\t"	     "ldarx	%0,0,%2\n"
			     "stdcx.	%3,0,%2\n"
			     "bne-	1b"
			     ISYNC_ON_SMP
			     : "=&r" (prev), "+m" (*(volatile unsigned long *)p)
			     : "r" (p), "r" (val)
			     : "cc", "memory");
	return prev;
}
#endif

static __always_inline
unsigned long __xchg(volatile void *ptr, unsigned long x, int size)
{
	switch (size) {
	case 4:
		return __xchg_u32(ptr, x);
#if (BITS_PER_LONG == 64)
	case 8:
		return __xchg_u64(ptr, x);
#endif
	}
	return x;
}

/*
 * note : xchg should only be used with pointers to 32 or 64-bits elements.
 * No build-time check is done on the element size because depending on
 * non-referenced unexisting symbol at link time to provide an error message
 * only work when compiling with optimizations.
 */
#define xchg(ptr, v)    \
	((__typeof__(*(ptr)))__xchg((ptr), (unsigned long)(v), sizeof(*(ptr))))

#endif /* #ifndef _INCLUDE_API_H */

#define mftbl()						\
	({ 						\
		unsigned long rval;			\
		asm volatile("mftbl %0" : "=r" (rval));	\
		rval;					\
	})

#define mftbu()						\
	({						\
		unsigned long rval;			\
		asm volatile("mftbu %0" : "=r" (rval));	\
		rval;					\
	})

typedef unsigned long long cycles_t;

static inline cycles_t get_cycles (void)
{
	long h, l;

	for (;;) {
		h = mftbu();
		barrier();
		l = mftbl();
		barrier();
		if (mftbu() == h)
			return (((cycles_t) h) << 32) + l;
	}
}

#endif /* _ARCH_PPC_H */
