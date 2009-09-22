#ifndef _ARCH_ATOMIC_X86_H
#define _ARCH_ATOMIC_X86_H

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

#ifndef _INCLUDE_API_H

/*
 * Derived from AO_compare_and_swap() and AO_test_and_set_full().
 */

struct __atomic_dummy {
	unsigned long v[10];
};
#define __hp(x)	((struct __atomic_dummy *)(x))

/* cmpxchg */

static inline __attribute__((always_inline))
unsigned long _atomic_cmpxchg(volatile void *addr, unsigned long old,
		unsigned long _new, int len)
{
	switch (len) {
	case 1:
	{
		unsigned char result = old;
		__asm__ __volatile__(
		"lock; cmpxchgb %2, %1"
			: "+a"(result), "+m"(*__hp(addr))
			: "q"((unsigned char)_new)
			: "memory");
		return result;
	}
	case 2:
	{
		unsigned short result = old;
		__asm__ __volatile__(
		"lock; cmpxchgw %2, %1"
			: "+a"(result), "+m"(*__hp(addr))
			: "r"((unsigned short)_new)
			: "memory");
		return result;
	}
	case 4:
	{
		unsigned int result = old;
		__asm__ __volatile__(
		"lock; cmpxchgl %2, %1"
			: "+a"(result), "+m"(*__hp(addr))
			: "r"((unsigned int)_new)
			: "memory");
		return result;
	}
#if (BITS_PER_LONG == 64)
	case 8:
	{
		unsigned int result = old;
		__asm__ __volatile__(
		"lock; cmpxchgl %2, %1"
			: "+a"(result), "+m"(*__hp(addr))
			: "r"((unsigned long)_new)
			: "memory");
		return result;
	}
#endif
	}
	/* generate an illegal instruction. Cannot catch this with linker tricks
	 * when optimizations are disabled. */
	__asm__ __volatile__("ud2");
	return 0;
}

#define cmpxchg(addr, old, _new)					    \
	((__typeof__(*(addr))) _atomic_cmpxchg((addr), (unsigned long)(old),\
						(unsigned long)(_new), 	    \
						sizeof(*(addr))))

/* xchg */

static inline __attribute__((always_inline))
unsigned long _atomic_exchange(volatile void *addr, unsigned long val, int len)
{
	/* Note: the "xchg" instruction does not need a "lock" prefix. */
	switch (len) {
	case 1:
	{
		unsigned char result;
		__asm__ __volatile__(
		"xchgb %0, %1"
			: "=q"(result), "+m"(*__hp(addr))
			: "0" ((unsigned char)val)
			: "memory");
		return result;
	}
	case 2:
	{
		unsigned short result;
		__asm__ __volatile__(
		"xchgw %0, %1"
			: "=r"(result), "+m"(*__hp(addr))
			: "0" ((unsigned short)val)
			: "memory");
		return result;
	}
	case 4:
	{
		unsigned int result;
		__asm__ __volatile__(
		"xchgl %0, %1"
			: "=r"(result), "+m"(*__hp(addr))
			: "0" ((unsigned int)val)
			: "memory");
		return result;
	}
#if (BITS_PER_LONG == 64)
	case 8:
	{
		unsigned long result;
		__asm__ __volatile__(
		"xchgq %0, %1"
			: "=r"(result), "+m"(*__hp(addr))
			: "0" ((unsigned long)val)
			: "memory");
		return result;
	}
#endif
	}
	/* generate an illegal instruction. Cannot catch this with linker tricks
	 * when optimizations are disabled. */
	__asm__ __volatile__("ud2");
	return 0;
}

#define xchg(addr, v)							    \
	((__typeof__(*(addr))) _atomic_exchange((addr), (unsigned long)(v), \
						sizeof(*(addr))))

/* atomic_add */

static inline __attribute__((always_inline))
void _atomic_add(volatile void *addr, unsigned long val, int len)
{
	switch (len) {
	case 1:
	{
		__asm__ __volatile__(
		"lock; addb %1, %0"
			: "=m"(*__hp(addr))
			: "iq" ((unsigned char)val)
			: "memory");
		return;
	}
	case 2:
	{
		__asm__ __volatile__(
		"lock; addw %1, %0"
			: "=m"(*__hp(addr))
			: "ir" ((unsigned short)val)
			: "memory");
		return;
	}
	case 4:
	{
		__asm__ __volatile__(
		"lock; addl %1, %0"
			: "=m"(*__hp(addr))
			: "ir" ((unsigned int)val)
			: "memory");
		return;
	}
#if (BITS_PER_LONG == 64)
	case 8:
	{
		__asm__ __volatile__(
		"lock; addq %1, %0"
			: "=m"(*__hp(addr))
			: "er" ((unsigned long)val)
			: "memory");
		return;
	}
#endif
	}
	/* generate an illegal instruction. Cannot catch this with linker tricks
	 * when optimizations are disabled. */
	__asm__ __volatile__("ud2");
	return;
}

#define atomic_add(addr, v)						   \
	(_atomic_add((addr), (unsigned long)(v), sizeof(*(addr))))

#endif /* #ifndef _INCLUDE_API_H */

#endif /* ARCH_ATOMIC_X86_H */
