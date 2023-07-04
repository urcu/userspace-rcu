// SPDX-FileCopyrightText: 1991-1994 by Xerox Corporation.  All rights reserved.
// SPDX-FileCopyrightText: 1996-1999 by Silicon Graphics.  All rights reserved.
// SPDX-FileCopyrightText: 1999-2004 Hewlett-Packard Development Company, L.P.
// SPDX-FileCopyrightText: 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
// SPDX-FileCopyrightText: 2010 Paul E. McKenney, IBM Corporation
//
// SPDX-License-Identifier: LicenseRef-Boehm-GC

#ifndef _URCU_ARCH_UATOMIC_ARM_H
#define _URCU_ARCH_UATOMIC_ARM_H

/*
 * Atomics for ARM.  This approach is usable on kernels back to 2.6.15.
 *
 * Code inspired from libuatomic_ops-1.2, inherited in part from the
 * Boehm-Demers-Weiser conservative garbage collector.
 */

#include <urcu/compiler.h>
#include <urcu/system.h>
#include <urcu/arch.h>

#ifdef __cplusplus
extern "C" {
#endif

/* xchg */

/*
 * Based on [1], __sync_lock_test_and_set() is not a full barrier, but
 * instead only an acquire barrier. Given that uatomic_xchg() acts as
 * both release and acquire barriers, we therefore need to have our own
 * release barrier before this operation.
 *
 * [1] https://gcc.gnu.org/onlinedocs/gcc-4.1.0/gcc/Atomic-Builtins.html
 */
#define uatomic_xchg(addr, v)				\
	({						\
		cmm_smp_mb();				\
		__sync_lock_test_and_set(addr, v);	\
	})

#ifdef __cplusplus
}
#endif

#include <urcu/uatomic/generic.h>

#endif /* _URCU_ARCH_UATOMIC_ARM_H */
