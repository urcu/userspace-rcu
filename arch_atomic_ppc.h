#ifndef _ARCH_ATOMIC_PPC_H
#define _ARCH_ATOMIC_PPC_H

/* 
 * Copyright (c) 1991-1994 by Xerox Corporation.  All rights reserved.
 * Copyright (c) 1996-1999 by Silicon Graphics.  All rights reserved.
 * Copyright (c) 1999-2004 Hewlett-Packard Development Company, L.P.
 * Copyright (c) 2009      Mathieu Desnoyers
 *
 * THIS MATERIAL IS PROVIDED AS IS, WITH ABSOLUTELY NO WARRANTY EXPRESSED
 * OR IMPLIED.  ANY USE IS AT YOUR OWN RISK.
 *
 * Permission is hereby granted to use or copy this program
 * for any purpose,  provided the above notices are retained on all copies.
 * Permission to modify the code and to distribute modified code is granted,
 * provided the above notices are retained, and a notice that the code was
 * modified is included with the above copyright notice.
 *
 * Code inspired from libatomic_ops-1.2, inherited in part from the
 * Boehm-Demers-Weiser conservative garbage collector.
 */

#ifndef BITS_PER_LONG
#define BITS_PER_LONG	(__SIZEOF_LONG__ * 8)
#endif

#define ILLEGAL_INSTR	".long	0xd00d00"

#ifndef _INCLUDE_API_H

/*
 * Using a isync as second barrier for exchange to provide acquire semantic.
 * According to atomic_ops/sysdeps/gcc/powerpc.h, the documentation is "fairly
 * explicit that this also has acquire semantics."
 * Derived from AO_compare_and_swap(), but removed the comparison.
 */

static __attribute__((always_inline))
unsigned int atomic_exchange_32(volatile unsigned int *addr, unsigned int val)
{
	unsigned int result;

	__asm__ __volatile__(
		"lwsync\n"
	"1:\t"	"lwarx %0,0,%1\n"	/* load and reserve */
		"stwcx. %2,0,%1\n"	/* else store conditional */
		"bne- 1b\n"	 	/* retry if lost reservation */
		"isync\n"
			: "=&r"(result)
			: "r"(addr), "r"(val)
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
		"lwsync\n"
	"1:\t"	"ldarx %0,0,%1\n"	/* load and reserve */
		"stdcx. %2,0,%1\n"	/* else store conditional */
		"bne- 1b\n"	 	/* retry if lost reservation */
		"isync\n"
			: "=&r"(result),
			: "r"(addr), "r"(val)
			: "memory", "cc");

	return result;
}

#endif

static __attribute__((always_inline))
unsigned long _atomic_exchange(volatile void *addr, unsigned long val, int len)
{
	switch (len) {
	case 4:	return atomic_exchange_32(addr, val);
#if (BITS_PER_LONG == 64)
	case 8:	return atomic_exchange_64(addr, val);
#endif
	}
	/* generate an illegal instruction. Cannot catch this with linker tricks
	 * when optimizations are disabled. */
	__asm__ __volatile__(ILLEGAL_INSTR);
	return 0;
}

#define xchg(addr, v)	(__typeof__(*(addr))) _atomic_exchange((addr), (v), \
							    sizeof(*(addr)))

#endif /* #ifndef _INCLUDE_API_H */

#endif /* ARCH_ATOMIC_PPC_H */
