// SPDX-License-Identifier: LGPL-2.1-or-later
// SPDX-FileCopyrightText: 2025 Olivier Dion <odion@efficios.com>
//

/*
 * urcu/uatomic/builtins-x86.h
 */

#ifndef _URCU_UATOMIC_BUILTINS_X86_H
#define _URCU_UATOMIC_BUILTINS_X86_H

/*
 * On x86, a atomic store with sequential consistency is always implemented with
 * an exchange operation, which has an implicit lock prefix when a memory operand
 * is used.
 *
 * Indeed, on x86, only loads can be re-ordered with prior stores. Therefore,
 * for keeping sequential consistency, either load operations or store
 * operations need to have a memory barrier. All major toolchains have selected
 * the store operations to have this barrier to avoid penalty on load
 * operations.
 *
 * Therefore, assuming that the used toolchain follows this convention, it is
 * safe to rely on this implicit memory barrier to implement the
 * `CMM_SEQ_CST_FENCE` memory order and thus no further barrier need to be
 * emitted.
 */
#define cmm_seq_cst_fence_after_atomic_store(...)	\
	do { } while (0)

/*
 * Let the default implementation (emit a memory barrier) after load operations
 * for the `CMM_SEQ_CST_FENCE`.  The rationale is explained above for
 * `cmm_seq_cst_fence_after_atomic_store()`.
 */
/* #define cmm_seq_cst_fence_after_atomic_load(...) */


/*
 * On x86, atomic read-modify-write operations always have a lock prefix either
 * implicitly or explicitly for sequential consistency.
 *
 * Therefore, no further memory barrier, for the `CMM_SEQ_CST_FENCE` memory
 * order, needs to be emitted for these operations.
 */
#define cmm_seq_cst_fence_after_atomic_rmw(...)	\
	do { } while (0)

#endif	/* _URCU_UATOMIC_BUILTINS_X86_H */
