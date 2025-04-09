// SPDX-FileCopyrightText: 1991-1994 by Xerox Corporation.  All rights reserved.
// SPDX-FileCopyrightText: 1996-1999 by Silicon Graphics.  All rights reserved.
// SPDX-FileCopyrightText: 1999-2004 Hewlett-Packard Development Company, L.P.
// SPDX-FileCopyrightText: 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
//
// SPDX-License-Identifier: LicenseRef-Boehm-GC

#ifndef _URCU_ARCH_UATOMIC_PPC_H
#define _URCU_ARCH_UATOMIC_PPC_H

/*
 * Code inspired from libuatomic_ops-1.2, inherited in part from the
 * Boehm-Demers-Weiser conservative garbage collector.
 */

#include <urcu/compiler.h>
#include <urcu/system.h>

#ifdef __cplusplus
extern "C" {
#endif

/* #define UATOMIC_HAS_ATOMIC_BYTE */
/* #define UATOMIC_HAS_ATOMIC_SHORT */
#define UATOMIC_HAS_ATOMIC_INT
#if (CAA_BITS_PER_LONG == 64)
#define UATOMIC_HAS_ATOMIC_LLONG
#endif

/* Must be included after the UATOMIC_HAS_ATOMIC_* defines. */
#include <urcu/uatomic/uassert.h>

/*
 * Providing sequential consistency semantic with respect to other
 * instructions for cmpxchg and add_return family of atomic primitives.
 *
 * This is achieved with:
 *   lwsync (prior stores can be reordered after following loads)
 *   lwarx
 *   stwcx.
 *   test if success (retry)
 *   sync
 *
 * Explanation of the sequential consistency provided by this scheme
 * from Paul E. McKenney:
 *
 * The reason we can get away with the lwsync before is that if a prior
 * store reorders with the lwarx, then you have to store to the atomic
 * variable from some other CPU to detect it.
 *
 * And if you do that, the lwarx will lose its reservation, so the stwcx
 * will fail.  The atomic operation will retry, so that the caller won't be
 * able to see the misordering.
 */

/* xchg */

static inline __attribute__((__always_inline__))
unsigned long _uatomic_exchange(void *addr, unsigned long val, int len)
{
	switch (len) {
	case 4:
	{
		unsigned int result;

		__asm__ __volatile__(
			LWSYNC_OPCODE
		"1:\t"	"lwarx %0,0,%1\n"	/* load and reserve */
			"stwcx. %2,0,%1\n"	/* else store conditional */
			"bne- 1b\n"	 	/* retry if lost reservation */
			"sync\n"
				: "=&r"(result)
				: "r"(addr), "r"(val)
				: "memory", "cc");

		return result;
	}
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
	{
		unsigned long result;

		__asm__ __volatile__(
			LWSYNC_OPCODE
		"1:\t"	"ldarx %0,0,%1\n"	/* load and reserve */
			"stdcx. %2,0,%1\n"	/* else store conditional */
			"bne- 1b\n"	 	/* retry if lost reservation */
			"sync\n"
				: "=&r"(result)
				: "r"(addr), "r"(val)
				: "memory", "cc");

		return result;
	}
#endif
	}
	return 0;
}

#define uatomic_xchg_mo(addr, v, mo)						\
	__extension__								\
	({									\
		_uatomic_static_assert_atomic(sizeof(*(addr)));			\
		(__typeof__(*(addr))) _uatomic_exchange((addr),			\
						caa_cast_long_keep_sign(v),	\
						sizeof(*(addr)));		\
	})

/* cmpxchg */

static inline __attribute__((__always_inline__))
unsigned long _uatomic_cmpxchg(void *addr, unsigned long old,
			      unsigned long _new, int len)
{
	switch (len) {
	case 4:
	{
		unsigned int old_val;

		__asm__ __volatile__(
			LWSYNC_OPCODE
		"1:\t"	"lwarx %0,0,%1\n"	/* load and reserve */
			"cmpw %0,%3\n"		/* if load is not equal to */
			"bne 2f\n"		/* old, fail */
			"stwcx. %2,0,%1\n"	/* else store conditional */
			"bne- 1b\n"	 	/* retry if lost reservation */
			"sync\n"
		"2:\n"
				: "=&r"(old_val)
				: "r"(addr), "r"((unsigned int)_new),
				  "r"((unsigned int)old)
				: "memory", "cc");

		return old_val;
	}
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
	{
		unsigned long old_val;

		__asm__ __volatile__(
			LWSYNC_OPCODE
		"1:\t"	"ldarx %0,0,%1\n"	/* load and reserve */
			"cmpd %0,%3\n"		/* if load is not equal to */
			"bne 2f\n"		/* old, fail */
			"stdcx. %2,0,%1\n"	/* else store conditional */
			"bne- 1b\n"	 	/* retry if lost reservation */
			"sync\n"
		"2:\n"
				: "=&r"(old_val)
				: "r"(addr), "r"((unsigned long)_new),
				  "r"((unsigned long)old)
				: "memory", "cc");

		return old_val;
	}
#endif
	}
	return 0;
}


#define uatomic_cmpxchg_mo(addr, old, _new, mos, mof)				\
	__extension__								\
	({									\
		_uatomic_static_assert_atomic(sizeof(*(addr)));			\
		(__typeof__(*(addr))) _uatomic_cmpxchg((addr),			\
						caa_cast_long_keep_sign(old),	\
						caa_cast_long_keep_sign(_new),	\
						sizeof(*(addr)));		\
	})

/* uatomic_add_return */

static inline __attribute__((__always_inline__))
unsigned long _uatomic_add_return(void *addr, unsigned long val,
				 int len)
{
	switch (len) {
	case 4:
	{
		unsigned int result;

		__asm__ __volatile__(
			LWSYNC_OPCODE
		"1:\t"	"lwarx %0,0,%1\n"	/* load and reserve */
			"add %0,%2,%0\n"	/* add val to value loaded */
			"stwcx. %0,0,%1\n"	/* store conditional */
			"bne- 1b\n"	 	/* retry if lost reservation */
			"sync\n"
				: "=&r"(result)
				: "r"(addr), "r"(val)
				: "memory", "cc");

		return result;
	}
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
	{
		unsigned long result;

		__asm__ __volatile__(
			LWSYNC_OPCODE
		"1:\t"	"ldarx %0,0,%1\n"	/* load and reserve */
			"add %0,%2,%0\n"	/* add val to value loaded */
			"stdcx. %0,0,%1\n"	/* store conditional */
			"bne- 1b\n"	 	/* retry if lost reservation */
			"sync\n"
				: "=&r"(result)
				: "r"(addr), "r"(val)
				: "memory", "cc");

		return result;
	}
#endif
	}
	return 0;
}


#define uatomic_add_return_mo(addr, v, mo)					\
	__extension__								\
	({									\
		_uatomic_static_assert_atomic(sizeof(*(addr)));			\
		(__typeof__(*(addr))) _uatomic_add_return((addr),		\
						caa_cast_long_keep_sign(v),	\
						sizeof(*(addr)));		\
	})

#ifdef __cplusplus
}
#endif

#include <urcu/uatomic/generic.h>

#endif /* _URCU_ARCH_UATOMIC_PPC_H */
