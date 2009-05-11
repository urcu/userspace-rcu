#ifndef _ARCH_PPC_H
#define _ARCH_PPC_H

/*
 * arch_x86.h: Definitions for the x86 architecture, derived from Linux.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; but only version 2 of the License given
 * that this comes from the Linux kernel.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 */

#include <compiler.h>

#define CONFIG_HAVE_FENCE 1
#define CONFIG_HAVE_MEM_COHERENCY

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

#ifndef _INCLUDE_API_H

static __inline__ void atomic_inc(int *v)
{
	int t;

	__asm__ __volatile__(
"1:	lwarx	%0,0,%2		# atomic_inc\n\
	addic	%0,%0,1\n"
	PPC405_ERR77(0,%2)
"	stwcx.	%0,0,%2 \n\
	bne-	1b"
	: "=&r" (t), "+m" (v)
	: "r" (&v)
	: "cc", "xer");
}

#endif /* #ifndef _INCLUDE_API_H */

struct __xchg_dummy {
	unsigned long a[100];
};
#define __xg(x) ((struct __xchg_dummy *)(x))

#ifndef _INCLUDE_API_H

/*
 * Atomic exchange
 *
 * Changes the memory location '*ptr' to be val and returns
 * the previous value stored there.
 */
static __always_inline unsigned long
__xchg_u32(volatile void *p, unsigned long val)
{
	unsigned long prev;

	__asm__ __volatile__(
	LWSYNC_ON_SMP
"1:	lwarx	%0,0,%2 \n"
	PPC405_ERR77(0,%2)
"	stwcx.	%3,0,%2 \n\
	bne-	1b"
	ISYNC_ON_SMP
	: "=&r" (prev), "+m" (*(volatile unsigned int *)p)
	: "r" (p), "r" (val)
	: "cc", "memory");

	return prev;
}

/*
 * This function doesn't exist, so you'll get a linker error
 * if something tries to do an invalid xchg().
 */
extern void __xchg_called_with_bad_pointer(void);

static __always_inline unsigned long
__xchg(volatile void *ptr, unsigned long x, unsigned int size)
{
	switch (size) {
	case 4:
		return __xchg_u32(ptr, x);
#ifdef CONFIG_PPC64
	case 8:
		return __xchg_u64(ptr, x);
#endif
	}
	__xchg_called_with_bad_pointer();
	return x;
}

#define xchg(ptr,x)							     \
  ({									     \
     __typeof__(*(ptr)) _x_ = (x);					     \
     (__typeof__(*(ptr))) __xchg((ptr), (unsigned long)_x_, sizeof(*(ptr))); \
  })

#endif /* #ifndef _INCLUDE_API_H */

#define mftbl()		({unsigned long rval;	\
			asm volatile("mftbl %0" : "=r" (rval)); rval;})
#define mftbu()		({unsigned long rval;	\
			asm volatile("mftbu %0" : "=r" (rval)); rval;})

typedef unsigned long long cycles_t;

static inline cycles_t get_cycles (void)
{
	long h;
	long l;

	for (;;) {
		h = mftbu();
		smp_mb();
		l = mftbl();
		smp_mb();
		if (mftbu() == h)
			return (((long long)h) << 32) + l;
	}
}

#endif /* _ARCH_PPC_H */
