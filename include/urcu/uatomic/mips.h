// SPDX-FileCopyrightText: 2010 Paolo Bonzini <pbonzini@redhat.com>
//
// SPDX-License-Identifier: MIT

#ifndef _URCU_UATOMIC_ARCH_MIPS_H
#define _URCU_UATOMIC_ARCH_MIPS_H

/*
 * Atomic exchange operations for the MIPS architecture. Let GCC do it.
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

#ifdef __cplusplus
}
#endif

#include <urcu/uatomic/generic.h>

#endif /* _URCU_UATOMIC_ARCH_MIPS_H */
