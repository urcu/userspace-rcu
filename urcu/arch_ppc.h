#ifndef _URCU_ARCH_PPC_H
#define _URCU_ARCH_PPC_H

/*
 * arch_ppc.h: trivial definitions for the powerpc architecture.
 *
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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

/* Include size of POWER5+ L3 cache lines: 256 bytes */
#define CAA_CACHE_LINE_SIZE	256

#define cmm_mb()    asm volatile("sync":::"memory")

#define mftbl()						\
	({ 						\
		unsigned long rval;			\
		asm volatile("mftbl %0" : "=r" (rval));	\
		rval;					\
	})

#define mftbu()						\
	({						\
		unsigned long rval;			\
		asm volatile("mftbu %0" : "=r" (rval));	\
		rval;					\
	})

typedef unsigned long long cycles_t;

static inline cycles_t caa_get_cycles (void)
{
	long h, l;

	for (;;) {
		h = mftbu();
		cmm_barrier();
		l = mftbl();
		cmm_barrier();
		if (mftbu() == h)
			return (((cycles_t) h) << 32) + l;
	}
}

#ifdef __cplusplus 
}
#endif

#include <urcu/arch_generic.h>

#endif /* _URCU_ARCH_PPC_H */
