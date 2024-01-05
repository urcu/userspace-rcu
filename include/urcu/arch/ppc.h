// SPDX-FileCopyrightText: 2009 Paul E. McKenney, IBM Corporation.
// SPDX-FileCopyrightText: 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
//
// SPDX-License-Identifier: LGPL-2.1-or-later

#ifndef _URCU_ARCH_PPC_H
#define _URCU_ARCH_PPC_H

/*
 * arch_ppc.h: trivial definitions for the powerpc architecture.
 */

#include <urcu/compiler.h>
#include <urcu/config.h>
#include <urcu/syscall-compat.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Include size of POWER5+ L3 cache lines: 256 bytes */
#define CAA_CACHE_LINE_SIZE	256

#ifdef __NO_LWSYNC__
#define LWSYNC_OPCODE	"sync\n"
#else
#define LWSYNC_OPCODE	"lwsync\n"
#endif

/*
 * Use sync for all cmm_mb/rmb/wmb barriers because lwsync does not
 * preserve ordering of cacheable vs. non-cacheable accesses, so it
 * should not be used to order with respect to MMIO operations.  An
 * eieio+lwsync pair is also not enough for cmm_rmb, because it will
 * order cacheable and non-cacheable memory operations separately---i.e.
 * not the latter against the former.
 */
#define cmm_mb()         __asm__ __volatile__ ("sync":::"memory")

/*
 * lwsync orders loads in cacheable memory with respect to other loads,
 * and stores in cacheable memory with respect to other stores.
 * Therefore, use it for barriers ordering accesses to cacheable memory
 * only.
 */
#define cmm_smp_rmb()    __asm__ __volatile__ (LWSYNC_OPCODE:::"memory")
#define cmm_smp_wmb()    __asm__ __volatile__ (LWSYNC_OPCODE:::"memory")

#define mftbl()						\
	__extension__					\
	({ 						\
		unsigned long rval;			\
		__asm__ __volatile__ ("mftb %0" : "=r" (rval));	\
		rval;					\
	})

#define mftbu()						\
	__extension__					\
	({						\
		unsigned long rval;			\
		__asm__ __volatile__ ("mftbu %0" : "=r" (rval));	\
		rval;					\
	})

#define mftb()						\
	__extension__					\
	({						\
		unsigned long long rval;		\
		__asm__ __volatile__ ("mftb %0" : "=r" (rval));		\
		rval;					\
	})

#define HAS_CAA_GET_CYCLES

typedef uint64_t caa_cycles_t;

#ifdef __powerpc64__
static inline caa_cycles_t caa_get_cycles(void)
{
	return (caa_cycles_t) mftb();
}
#else
static inline caa_cycles_t caa_get_cycles(void)
{
	unsigned long h, l;

	for (;;) {
		h = mftbu();
		cmm_barrier();
		l = mftbl();
		cmm_barrier();
		if (mftbu() == h)
			return (((caa_cycles_t) h) << 32) + l;
	}
}
#endif

/*
 * On Linux, define the membarrier system call number if not yet available in
 * the system headers.
 */
#if (defined(__linux__) && !defined(__NR_membarrier))
#define __NR_membarrier		365
#endif

#ifdef __cplusplus
}
#endif

#include <urcu/arch/generic.h>

#endif /* _URCU_ARCH_PPC_H */
