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

#define cpu_relax()	asm volatile("rep; nop" : : : "memory");

/*
 * Serialize core instruction execution. Also acts as a compiler barrier.
 * On PIC ebx cannot be clobbered
 */
#ifdef __PIC__
#define sync_core()							  \
	asm volatile("push %%ebx; cpuid; pop %%ebx"			  \
		     : : : "memory", "eax", "ecx", "edx");
#endif
#ifndef __PIC__
#define sync_core()							  \
	asm volatile("cpuid" : : : "memory", "eax", "ebx", "ecx", "edx");
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

#include <urcu/arch_generic.h>

#endif /* _URCU_ARCH_X86_H */
