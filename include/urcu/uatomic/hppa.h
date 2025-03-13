// SPDX-FileCopyrightText: 2014 Helge Deller <deller@gmx.de>
//
// SPDX-License-Identifier: LGPL-2.1-or-later

#ifndef _URCU_ARCH_UATOMIC_HPPA_H
#define _URCU_ARCH_UATOMIC_HPPA_H

#include <urcu/compiler.h>
#include <urcu/system.h>

/* #define UATOMIC_HAS_ATOMIC_BYTE */
#define UATOMIC_HAS_ATOMIC_SHORT
#define UATOMIC_HAS_ATOMIC_INT
#if (CAA_BITS_PER_LONG == 64)
#define UATOMIC_HAS_ATOMIC_LLONG
#endif

#include <urcu/uatomic/generic.h>

#endif /* _URCU_ARCH_UATOMIC_HPPA_H */
