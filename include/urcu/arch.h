/*
 * urcu/arch.h
 *
 * Copyright (c) 2020 Michael Jeanson <michael.jeanson@efficios.com>
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

#ifndef _URCU_ARCH_H
#define _URCU_ARCH_H

/*
 * Architecture detection using compiler defines.
 *
 * The following defines are used internally for architecture specific code.
 *
 * URCU_ARCH_X86 : All x86 variants 32 and 64 bits
 *   URCU_ARCH_I386 : Specific to the i386
 *   URCU_ARCH_AMD64 : All 64 bits x86 variants
 *   URCU_ARCH_K1OM : Specific to the Xeon Phi / MIC
 *
 * URCU_ARCH_PPC : All PowerPC variants 32 and 64 bits
 *   URCU_ARCH_PPC64 : Specific to 64 bits variants
 *
 * URCU_ARCH_S390 : All IBM s390 / s390x variants
 *
 * URCU_ARCH_SPARC64 : All Sun SPARC variants
 *
 * URCU_ARCH_ALPHA : All DEC Alpha variants
 * URCU_ARCH_IA64 : All Intel Itanium variants
 * URCU_ARCH_ARM : All ARM 32 bits variants
 *   URCU_ARCH_ARMV7 : All ARMv7 ISA variants
 * URCU_ARCH_AARCH64 : All ARM 64 bits variants
 * URCU_ARCH_MIPS : All MIPS variants
 * URCU_ARCH_NIOS2 : All Intel / Altera NIOS II variants
 * URCU_ARCH_TILE : All Tilera TILE variants
 * URCU_ARCH_HPPA : All HP PA-RISC variants
 * URCU_ARCH_M68K : All Motorola 68000 variants
 * URCU_ARCH_RISCV : All RISC-V variants
 * URCU_ARCH_LOONGARCH : All LoongArch variants
 */

#if (defined(__INTEL_OFFLOAD) || defined(__TARGET_ARCH_MIC) || defined(__MIC__))

#define URCU_ARCH_X86 1
#define URCU_ARCH_AMD64 1
#define URCU_ARCH_K1OM 1
#include <urcu/arch/x86.h>

#elif (defined(__amd64__) || defined(__amd64) || defined(__x86_64__) || defined(__x86_64))

#define URCU_ARCH_X86 1
#define URCU_ARCH_AMD64 1
#include <urcu/arch/x86.h>

#elif (defined(__i386__) || defined(__i386))

#define URCU_ARCH_X86 1

/*
 * URCU_ARCH_X86_NO_CAS enables a compat layer that will detect the presence of
 * the cmpxchg instructions at runtime and provide a compat mode based on a
 * pthread mutex when it isn't.
 *
 * __GCC_HAVE_SYNC_COMPARE_AND_SWAP_4 was introduced in GCC 4.3 and Clang 3.3,
 * building with older compilers will result in the compat layer always being
 * used on x86-32.
 */
#ifndef __GCC_HAVE_SYNC_COMPARE_AND_SWAP_4
#define URCU_ARCH_X86_NO_CAS 1
/* For backwards compat */
#define URCU_ARCH_I386 1
#endif

#include <urcu/arch/x86.h>

#elif (defined(__powerpc64__) || defined(__ppc64__))

#define URCU_ARCH_PPC 1
#define URCU_ARCH_PPC64 1
#include <urcu/arch/ppc.h>

#elif (defined(__powerpc__) || defined(__powerpc) || defined(__ppc__))

#define URCU_ARCH_PPC 1
#include <urcu/arch/ppc.h>

#elif (defined(__s390__) || defined(__s390x__) || defined(__zarch__))

#define URCU_ARCH_S390 1
#include <urcu/arch/s390.h>

#elif (defined(__sparc__) || defined(__sparc) || defined(__sparc64__))

#define URCU_ARCH_SPARC64 1
#include <urcu/arch/sparc64.h>

#elif (defined(__alpha__) || defined(__alpha))

#define URCU_ARCH_ALPHA 1
#include <urcu/arch/alpha.h>

#elif (defined(__ia64__) || defined(__ia64))

#define URCU_ARCH_IA64 1
#include <urcu/arch/ia64.h>

#elif (defined(__ARM_ARCH_7A__) || defined(__ARM_ARCH_7__))

#define URCU_ARCH_ARMV7 1
#define URCU_ARCH_ARM 1
#include <urcu/arch/arm.h>

#elif (defined(__arm__) || defined(__arm))

#define URCU_ARCH_ARM 1
#include <urcu/arch/arm.h>

#elif defined(__aarch64__)

#define URCU_ARCH_AARCH64 1
#include <urcu/arch/aarch64.h>

#elif (defined(__mips__) || defined(__mips))

#define URCU_ARCH_MIPS 1
#include <urcu/arch/mips.h>

#elif (defined(__nios2__) || defined(__nios2))

#define URCU_ARCH_NIOS2 1
#include <urcu/arch/nios2.h>

#elif defined(__tilegx__)
/*
 * URCU has only been tested on the TileGx architecture. For other Tile*
 * architectures, please run the tests first and report the results to the
 * maintainer so that proper support can be added.
 */

#define URCU_ARCH_TILE 1
#include <urcu/arch/tile.h>

#elif (defined(__hppa__) || defined(__HPPA__) || defined(__hppa))

#define URCU_ARCH_HPPA 1
#include <urcu/arch/hppa.h>

#elif defined(__m68k__)

#define URCU_ARCH_M68K 1
#include <urcu/arch/m68k.h>

#elif defined(__riscv)

#define URCU_ARCH_RISCV 1
#include <urcu/arch/riscv.h>

#elif defined(__loongarch__)

#define URCU_ARCH_LOONGARCH 1
#include <urcu/arch/loongarch.h>

#else
#error "Cannot build: unrecognized architecture, see <urcu/arch.h>."
#endif


#endif /* _URCU_ARCH_H */
