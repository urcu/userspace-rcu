#ifndef _ARCH_S390_H
#define _ARCH_S390_H

/*
 * Trivial definitions for the S390 architecture.
 *
 * Copyright (C) 2009 Novell, Inc.
 * Author: Jan Blunck <jblunck@suse.de>
 *
 * Based on the Principles of Operation "CPU Serialization" (5-91), "BRANCH ON
 * CONDITION" (7-25) and "STORE CLOCK" (7-169).
 *
 * Inspired by arch_ppc.h which is:
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License version 2.1 as
 * published by the Free  Software Foundation.
 */

#include <compiler.h>
#include <arch_atomic.h>

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
