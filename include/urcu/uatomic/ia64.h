// SPDX-FileCopyrightText: 1991-1994 by Xerox Corporation.  All rights reserved.
// SPDX-FileCopyrightText: 1996-1999 by Silicon Graphics.  All rights reserved.
// SPDX-FileCopyrightText: 1999-2004 Hewlett-Packard Development Company, L.P.
// SPDX-FileCopyrightText: 2009-2015 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
// SPDX-FileCopyrightText: 2010 Paul E. McKenney, IBM Corporation
//
// SPDX-License-Identifier: LicenseRef-Boehm-GC

#ifndef _URCU_ARCH_UATOMIC_IA64_H
#define _URCU_ARCH_UATOMIC_IA64_H

/*
 * Code inspired from libuatomic_ops-1.2, inherited in part from the
 * Boehm-Demers-Weiser conservative garbage collector.
 */

#include <urcu/compiler.h>
#include <urcu/system.h>

#ifdef __cplusplus
extern "C" {
#endif

#define UATOMIC_HAS_ATOMIC_BYTE
#define UATOMIC_HAS_ATOMIC_SHORT
#define UATOMIC_HAS_ATOMIC_INT
#define UATOMIC_HAS_ATOMIC_LLONG

#ifdef __cplusplus
}
#endif

#include <urcu/uatomic/generic.h>

#endif /* _URCU_ARCH_UATOMIC_IA64_H */
