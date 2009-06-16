#ifndef _ARCH_ATOMIC_S390_H
#define _ARCH_ATOMIC_S390_H

/*
 * Atomic exchange operations for the S390 architecture.
 *
 * Copyright (C) 2009 Novell, Inc.
 * Author: Jan Blunck <jblunck@suse.de>
 *
 * This is taken from the Principles of Operation Appendix A "Conditional
 * Swapping Instructions (CS, CDS)".
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License version 2.1 as
 * published by the Free  Software Foundation.
 */

#ifndef __SIZEOF_LONG__
#ifdef __s390x__
#define __SIZEOF_LONG__ 8
#else
#define __SIZEOF_LONG__ 4
#endif
#endif

#ifndef BITS_PER_LONG
#define BITS_PER_LONG	(__SIZEOF_LONG__ * 8)
#endif

#ifndef _INCLUDE_API_H

static __attribute__((always_inline))
unsigned int atomic_exchange_32(volatile unsigned int *addr, unsigned int val)
{
	unsigned int result;

	__asm__ __volatile__(
		"0:	cs %0,%2,%1\n"
		"	brc 4,0b\n"
		: "=&r"(result), "=m" (*addr)
		: "r"(val), "m" (*addr)
		: "memory", "cc");

	return result;
}

#if (BITS_PER_LONG == 64)

static __attribute__((always_inline))
unsigned long atomic_exchange_64(volatile unsigned long *addr,
				 unsigned long val)
{
	unsigned long result;

	__asm__ __volatile__(
		"0:	csg %0,%2,%1\n"
		"	brc 4,0b\n"
		: "=&r"(result), "=m" (*addr)
		: "r"(val), "m" (*addr)
		: "memory", "cc");

	return result;
}

#endif

static __attribute__((always_inline))
unsigned long _atomic_exchange(volatile void *addr, unsigned long val, int len)
{
	switch (len) {
	case 4:
		return atomic_exchange_32(addr, val);
#if (BITS_PER_LONG == 64)
	case 8:
		return atomic_exchange_64(addr, val);
#endif
	default:
		__asm__ __volatile__(".long	0xd00d00");
	}

	return 0;
}

#define xchg(addr, v)	(__typeof__(*(addr))) _atomic_exchange((addr), (v), \
							       sizeof(*(addr)))

#endif /* #ifndef _INCLUDE_API_H */

#endif /* ARCH_ATOMIC_S390_H */
