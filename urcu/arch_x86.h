#ifndef _URCU_ARCH_X86_H
#define _URCU_ARCH_X86_H

/*
 * arch_x86.h: trivial definitions for the x86 architecture.
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

#define CACHE_LINE_SIZE	128

#ifdef CONFIG_RCU_HAVE_FENCE
#define mb()    asm volatile("mfence":::"memory")
#define rmb()   asm volatile("lfence":::"memory")
#define wmb()   asm volatile("sfence"::: "memory")
#else
/*
 * Some non-Intel clones support out of order store. wmb() ceases to be a
 * nop for these.
 */
#define mb()    asm volatile("lock; addl $0,0(%%esp)":::"memory")
#define rmb()   asm volatile("lock; addl $0,0(%%esp)":::"memory")
#define wmb()   asm volatile("lock; addl $0,0(%%esp)"::: "memory")
#endif

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

static inline void rep_nop(void)
{
	asm volatile("rep; nop" : : : "memory");
}

static inline void cpu_relax(void)
{
	rep_nop();
}

/*
 * Serialize core instruction execution. Also acts as a compiler barrier.
 */
#ifdef __PIC__
/*
 * Cannot use cpuid because it clobbers the ebx register and clashes
 * with -fPIC :
 * error: PIC register 'ebx' clobbered in 'asm'
 */
static inline void sync_core(void)
{
	mb();
}
#else
static inline void sync_core(void)
{
	asm volatile("cpuid" : : : "memory", "eax", "ebx", "ecx", "edx");
}
#endif

#define rdtscll(val)							  \
	do {						  		  \
	     unsigned int __a, __d;					  \
	     asm volatile("rdtsc" : "=a" (__a), "=d" (__d));		  \
	     (val) = ((unsigned long long)__a)				  \
			| (((unsigned long long)__d) << 32);		  \
	} while(0)

typedef unsigned long long cycles_t;

static inline cycles_t get_cycles(void)
{
        cycles_t ret = 0;

        rdtscll(ret);
        return ret;
}

#ifdef __cplusplus 
}
#endif

#endif /* _URCU_ARCH_X86_H */
