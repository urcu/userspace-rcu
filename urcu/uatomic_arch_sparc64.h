#ifndef _URCU_ARCH_UATOMIC_SPARC64_H
#define _URCU_ARCH_UATOMIC_SPARC64_H

/* 
 * Copyright (c) 1991-1994 by Xerox Corporation.  All rights reserved.
 * Copyright (c) 1996-1999 by Silicon Graphics.  All rights reserved.
 * Copyright (c) 1999-2003 by Hewlett-Packard Company. All rights reserved.
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
 * Code inspired from libuatomic_ops-1.2, inherited in part from the
 * Boehm-Demers-Weiser conservative garbage collector.
 */

#include <urcu/compiler.h>
#include <urcu/system.h>

#ifndef __SIZEOF_LONG__
#ifdef __LP64__
#define __SIZEOF_LONG__ 8
#else
#define __SIZEOF_LONG__ 4
#endif
#endif

#ifndef BITS_PER_LONG
#define BITS_PER_LONG	(__SIZEOF_LONG__ * 8)
#endif

#define uatomic_set(addr, v)	STORE_SHARED(*(addr), (v))
#define uatomic_read(addr)	LOAD_SHARED(*(addr))

/* cmpxchg */

static inline __attribute__((always_inline))
unsigned long _uatomic_cmpxchg(void *addr, unsigned long old,
			      unsigned long _new, int len)
{
	switch (len) {
	case 4:
	{
		__asm__ __volatile__ (
			"membar #StoreLoad | #LoadLoad\n\t"
                        "cas [%1],%2,%0\n\t"
                        "membar #StoreLoad | #StoreStore\n\t"
                        : "+&r" (_new)
                        : "r" (addr), "r" (old)
                        : "memory");

		return _new;
	}
#if (BITS_PER_LONG == 64)
	case 8:
	{
		__asm__ __volatile__ (
			"membar #StoreLoad | #LoadLoad\n\t"
                        "casx [%1],%2,%0\n\t"
                        "membar #StoreLoad | #StoreStore\n\t"
                        : "+&r" (_new)
                        : "r" (addr), "r" (old)
                        : "memory");

		return _new;
	}
#endif
	}
	__builtin_trap();
	return 0;
}


#define uatomic_cmpxchg(addr, old, _new)				    \
	((__typeof__(*(addr))) _uatomic_cmpxchg((addr), (unsigned long)(old),\
						(unsigned long)(_new), 	    \
						sizeof(*(addr))))

/* xchg */

static inline __attribute__((always_inline))
unsigned long _uatomic_exchange(void *addr, unsigned long val, int len)
{
	switch (len) {
	case 4:
	{
		unsigned int old, oldt;

		oldt = uatomic_read((unsigned int *)addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, val, 4);
		} while (oldt != old);

		return old;
	}
#if (BITS_PER_LONG == 64)
	case 8:
	{
		unsigned long old, oldt;

		oldt = uatomic_read((unsigned long *)addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, val, 8);
		} while (oldt != old);

		return old;
	}
#endif
	}
	__builtin_trap();
	return 0;
}

#define uatomic_xchg(addr, v)						    \
	((__typeof__(*(addr))) _uatomic_exchange((addr), (unsigned long)(v), \
						sizeof(*(addr))))

/* uatomic_add_return */

static inline __attribute__((always_inline))
unsigned long _uatomic_add_return(void *addr, unsigned long val,
				 int len)
{
	switch (len) {
	case 4:
	{
		unsigned int old, oldt;

		oldt = uatomic_read((unsigned int *)addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, old + val, 4);
		} while (oldt != old);

		return old + val;
	}
#if (BITS_PER_LONG == 64)
	case 8:
	{
		unsigned long old, oldt;

		oldt = uatomic_read((unsigned long *)addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, old + val, 8);
		} while (oldt != old);

		return old + val;
	}
#endif
	}
	__builtin_trap();
	return 0;
}

#define uatomic_add_return(addr, v)					\
	((__typeof__(*(addr))) _uatomic_add_return((addr),		\
						  (unsigned long)(v),	\
						  sizeof(*(addr))))

/* uatomic_sub_return, uatomic_add, uatomic_sub, uatomic_inc, uatomic_dec */

#define uatomic_sub_return(addr, v)	uatomic_add_return((addr), -(v))

#define uatomic_add(addr, v)		(void)uatomic_add_return((addr), (v))
#define uatomic_sub(addr, v)		(void)uatomic_sub_return((addr), (v))

#define uatomic_inc(addr)		uatomic_add((addr), 1)
#define uatomic_dec(addr)		uatomic_add((addr), -1)

#define URCU_CAS_AVAIL()	1
#define compat_uatomic_cmpxchg(ptr, old, _new)	uatomic_cmpxchg(ptr, old, _new)

#endif /* _URCU_ARCH_UATOMIC_PPC_H */
