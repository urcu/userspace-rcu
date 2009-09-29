#ifndef _ARCH_S390_H
#define _ARCH_S390_H

/*
 * Trivial definitions for the S390 architecture based on information from the
 * Principles of Operation "CPU Serialization" (5-91), "BRANCH ON CONDITION"
 * (7-25) and "STORE CLOCK" (7-169).
 *
 * Copyright (c) 2009 Novell, Inc.
 * Author: Jan Blunck <jblunck@suse.de>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 */

#include <compiler.h>

#define CONFIG_HAVE_MEM_COHERENCY
/* Assume SMP machine, given we don't have this information */
#define CONFIG_SMP 1

#ifndef BITS_PER_LONG
#define BITS_PER_LONG	(__SIZEOF_LONG__ * 8)
#endif

#define mb()    __asm__ __volatile__("bcr 15,0" : : : "memory")
#define rmb()   __asm__ __volatile__("bcr 15,0" : : : "memory");
#define wmb()   __asm__ __volatile__("bcr 15,0" : : : "memory");
#define mc()	barrier()
#define rmc()	barrier()
#define wmc()	barrier()

#define smp_mb()	mb()
#define smp_rmb()	rmb()
#define smp_wmb()	wmb()
#define smp_mc()	mc()
#define smp_rmc()	rmc()
#define smp_wmc()	wmc()

/* Nop everywhere except on alpha. */
#define smp_read_barrier_depends()

static inline void cpu_relax(void)
{
	barrier();
}

static inline void sync_core()
{
	__asm__ __volatile__("bcr 15,0" : : : "memory");
}

typedef unsigned long long cycles_t;

static inline cycles_t get_cycles (void)
{
	cycles_t cycles;

	__asm__ __volatile__("stck %0" : "=m" (cycles) : : "cc", "memory" );

	return cycles;
}

#endif /* _ARCH_S390_H */
