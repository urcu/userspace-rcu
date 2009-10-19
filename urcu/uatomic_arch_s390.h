#ifndef _URCU_ARCH_ATOMIC_S390_H
#define _URCU_ARCH_ATOMIC_S390_H

/*
 * Atomic exchange operations for the S390 architecture. Based on information
 * taken from the Principles of Operation Appendix A "Conditional Swapping
 * Instructions (CS, CDS)".
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

#include <urcu/compiler.h>
#include <urcu/system.h>

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

#define uatomic_set(addr, v)	STORE_SHARED(*(addr), (v))
#define uatomic_read(addr)	LOAD_SHARED(*(addr))

static inline __attribute__((always_inline))
unsigned int uatomic_exchange_32(volatile unsigned int *addr, unsigned int val)
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

static inline __attribute__((always_inline))
unsigned long uatomic_exchange_64(volatile unsigned long *addr,
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

static inline __attribute__((always_inline))
unsigned long _uatomic_exchange(volatile void *addr, unsigned long val, int len)
{
	switch (len) {
	case 4:
		return uatomic_exchange_32(addr, val);
#if (BITS_PER_LONG == 64)
	case 8:
		return uatomic_exchange_64(addr, val);
#endif
	default:
		__asm__ __volatile__(".long	0xd00d00");
	}

	return 0;
}

#define uatomic_xchg(addr, v)						\
	(__typeof__(*(addr))) _uatomic_exchange((addr), (unsigned long)(v), \
					       sizeof(*(addr)))


static inline __attribute__((always_inline))
void uatomic_add_32(volatile unsigned int *addr, unsigned int val)
{
	unsigned int result, old;

	__asm__ __volatile__(
		"	l %0, %1\n"
		"0:	lr %2, %0\n"
		"	ar %2, %3\n"
		"	cs %0,%2,%1\n"
		"	brc 4,0b\n"
		: "=&r"(old), "+m" (*addr),
		  "=&r"(result)
		: "r"(val)
		: "memory", "cc");
}

#if (BITS_PER_LONG == 64)

static inline __attribute__((always_inline))
void uatomic_add_64(volatile unsigned long *addr, unsigned long val)
{
	unsigned long result, old;

	__asm__ __volatile__(
		"	lg %0, %1\n"
		"0:	lgr %2, %0\n"
		"	agr %2, %3\n"
		"	csg %0,%2,%1\n"
		"	brc 4,0b\n"
		: "=&r"(old), "+m" (*addr),
		  "=&r"(result)
		: "r"(val)
		: "memory", "cc");
}

#endif

static inline __attribute__((always_inline))
void _uatomic_add(void *addr, unsigned long val, int len)
{
	switch (len) {
	case 4:
		uatomic_add_32(addr, val);
		return;
#if (BITS_PER_LONG == 64)
	case 8:
		uatomic_add_64(addr, val);
		return;
#endif
	default:
		__asm__ __volatile__(".long	0xd00d00");
	}

	return;
}

#define uatomic_add(addr, val)						\
	_uatomic_add((addr), (unsigned long)(val), sizeof(*(addr)))

static inline __attribute__((always_inline))
unsigned int uatomic_cmpxchg_32(volatile unsigned int *addr, unsigned int old,
				unsigned int new)
{
	__asm__ __volatile__(
		"	cs %0,%2,%1\n"
		: "+r"(old), "+m"(*addr)
		: "r"(new)
		: "memory", "cc");

	return old;
}

#if (BITS_PER_LONG == 64)

static inline __attribute__((always_inline))
unsigned long uatomic_cmpxchg_64(volatile unsigned long *addr,
				 unsigned long old, unsigned long new)
{
	__asm__ __volatile__(
		"	csg %0,%2,%1\n"
		: "+r"(old), "+m"(*addr)
		: "r"(new)
		: "memory", "cc");

	return old;
}

#endif

unsigned long _uatomic_cmpxchg(void *addr, unsigned long old,
			       unsigned long new, int len)
{
	switch (len) {
	case 4:
		return uatomic_cmpxchg_32(addr, old, new);
#if (BITS_PER_LONG == 64)
	case 8:
		return uatomic_cmpxchg_64(addr, old, new);
#endif
	default:
		__asm__ __volatile__(".long	0xd00d00");
	}

	return 0;
}

#define uatomic_cmpxchg(addr, old, new)					\
	(__typeof__(*(addr))) _uatomic_cmpxchg((addr),			\
					       (unsigned long)(old),	\
					       (unsigned long)(new),	\
					       sizeof(*(addr)))

#define URCU_CAS_AVAIL()	1

#endif /* _URCU_ARCH_ATOMIC_S390_H */
