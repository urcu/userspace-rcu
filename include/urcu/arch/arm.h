#ifndef _URCU_ARCH_ARM_H
#define _URCU_ARCH_ARM_H

/*
 * arch_arm.h: trivial definitions for the ARM architecture.
 *
 * Copyright (c) 2010 Paul E. McKenney, IBM Corporation.
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
#include <urcu/syscall-compat.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifdef CONFIG_RCU_ARM_HAVE_DMB
/*
 * Issues full system DMB operation.
 */
#define cmm_mb()	__asm__ __volatile__ ("dmb sy":::"memory")
#define cmm_rmb()	__asm__ __volatile__ ("dmb sy":::"memory")
#define cmm_wmb()	__asm__ __volatile__ ("dmb sy":::"memory")

/*
 * Issues DMB operation only to the inner shareable domain.
 */
#define cmm_smp_mb()	__asm__ __volatile__ ("dmb ish":::"memory")
#define cmm_smp_rmb()	__asm__ __volatile__ ("dmb ish":::"memory")
#define cmm_smp_wmb()	__asm__ __volatile__ ("dmb ish":::"memory")
#endif /* CONFIG_RCU_ARM_HAVE_DMB */

#include <stdlib.h>
#include <sys/time.h>

/*
 * On Linux, define the membarrier system call number if not yet available in
 * the system headers.
 */
#if (defined(__linux__) && !defined(__NR_membarrier))
#define __NR_membarrier		389
#endif

#ifdef __cplusplus
}
#endif

#include <urcu/arch/generic.h>

#endif /* _URCU_ARCH_ARM_H */
