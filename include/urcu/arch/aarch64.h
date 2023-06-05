#ifndef _URCU_ARCH_AARCH64_H
#define _URCU_ARCH_AARCH64_H

/*
 * arch/aarch64.h: definitions for aarch64 architecture
 *
 * Copyright (c) 2010 Paul E. McKenney, IBM Corporation.
 * Copyright (c) 2009-2015 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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
 * the system headers. aarch64 implements asm-generic/unistd.h system call
 * numbers.
 */
#if (defined(__linux__) && !defined(__NR_membarrier))
#define __NR_membarrier		283
#endif

/*
 * https://gcc.gnu.org/bugzilla/show_bug.cgi?id=63293
 *
 * Backported in RHEL7 gcc 4.8.5-11
 */
#if defined(URCU_GCC_VERSION) && defined(__GNUC_RH_RELEASE__)
# if (URCU_GCC_VERSION == 40805) && (__GNUC_RH_RELEASE__ >= 11)
#  define URCU_GCC_PATCHED_63293
# endif
#endif

#ifdef URCU_GCC_VERSION
# if URCU_GCC_VERSION < 50100 && !defined(URCU_GCC_PATCHED_63293)
#  error Your gcc version performs unsafe access to deallocated stack
# endif
#endif

#define caa_cpu_relax()	__asm__ __volatile__ ("yield" : : : "memory")

#ifdef __cplusplus
}
#endif

#include <urcu/arch/generic.h>

#endif /* _URCU_ARCH_AARCH64_H */
