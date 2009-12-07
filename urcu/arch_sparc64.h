#ifndef _URCU_ARCH_SPARC64_H
#define _URCU_ARCH_SPARC64_H

/*
 * arch_sparc64.h: trivial definitions for the Sparc64 architecture.
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

#define CACHE_LINE_SIZE	256

#ifndef BITS_PER_LONG
#define BITS_PER_LONG	(__SIZEOF_LONG__ * 8)
#endif

/*
 * Inspired from the Linux kernel. Workaround Spitfire bug #51.
 */
#define membar_safe(type)			\
__asm__ __volatile__("ba,pt %%xcc, 1f\n\t"	\
		     "membar " type "\n"	\
		     "1:\n"			\
		     : : : "memory")

#define mb()    membar_safe("#LoadLoad | #LoadStore | #StoreStore | #StoreLoad")
#define rmb()    membar_safe("#LoadLoad")
#define wmb()    membar_safe("#StoreStore")

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

#ifdef CONFIG_URCU_SMP
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
	mb();
}

typedef unsigned long long cycles_t;

static inline cycles_t get_cycles (void)
{
	return 0;	/* unimplemented */
}

#ifdef __cplusplus 
}
#endif

#endif /* _URCU_ARCH_SPARC64_H */
