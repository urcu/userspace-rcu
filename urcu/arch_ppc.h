#ifndef _URCU_ARCH_PPC_H
#define _URCU_ARCH_PPC_H

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

#include <urcu/compiler.h>
#include <urcu/config.h>

#ifdef __cplusplus
extern "C" {
#endif 

#define CONFIG_HAVE_MEM_COHERENCY

/* Include size of POWER5+ L3 cache lines: 256 bytes */
#define CACHE_LINE_SIZE	256

#ifndef BITS_PER_LONG
#define BITS_PER_LONG	(__SIZEOF_LONG__ * 8)
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

#ifdef CONFIG_RCU_SMP
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

/*
 * Serialize core instruction execution. Also acts as a compiler barrier.
 */
static inline void sync_core()
{
	asm volatile("isync" : : : "memory");
}

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

#ifdef __cplusplus 
}
#endif

#endif /* _URCU_ARCH_PPC_H */
