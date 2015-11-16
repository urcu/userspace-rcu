#ifndef _URCU_ARCH_HPPA_H
#define _URCU_ARCH_HPPA_H

/*
 * arch/hppa.h: definitions for hppa architecture
 *
 * Copyright (c) 2014 Helge Deller <deller@gmx.de>
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
#include <urcu/syscall-compat.h>

#ifdef __cplusplus
extern "C" {
#endif

#include <stdlib.h>
#include <sys/time.h>

/*
 * On Linux, define the membarrier system call number if not yet available in
 * the system headers.
 */
#if (defined(__linux__) && !defined(__NR_membarrier))
#define __NR_membarrier		343
#endif

#define HAS_CAA_GET_CYCLES
typedef unsigned long caa_cycles_t;

static inline caa_cycles_t caa_get_cycles(void)
{
	caa_cycles_t cycles;

	asm volatile("mfctl 16, %0" : "=r" (cycles));
	return cycles;
}

#ifdef __cplusplus
}
#endif

#include <urcu/arch/generic.h>

#endif /* _URCU_ARCH_HPPA_H */
