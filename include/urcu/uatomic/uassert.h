// SPDX-FileCopyrightText: 2025 Michael Jeanson <mjeanson@efficios.com>
//
// SPDX-License-Identifier: LGPL-2.1-or-later

#ifndef _URCU_ARCH_UATOMIC_UASSERT_H
#define _URCU_ARCH_UATOMIC_UASSERT_H

#include <urcu/compiler.h>

#ifdef __cplusplus
extern "C" {
#endif

#define _uatomic_str(s) #s
#define _uatomic_xstr(s) _uatomic_str(s)

#if (!(defined(UATOMIC_HAS_ATOMIC_BYTE) || \
	defined(UATOMIC_HAS_ATOMIC_SHORT) || \
	defined(UATOMIC_HAS_ATOMIC_INT) || \
	defined(UATOMIC_HAS_ATOMIC_LLONG)))
#error "This header must be included after the architecture UATOMIC_HAS_ATOMIC_* defines."
#endif

#ifdef UATOMIC_HAS_ATOMIC_BYTE
#define _UATOMIC_HAS_ATOMIC_BYTE_FLAG (1 << 0)
#else
#define _UATOMIC_HAS_ATOMIC_BYTE_FLAG (0)
#endif

#ifdef UATOMIC_HAS_ATOMIC_SHORT
#define _UATOMIC_HAS_ATOMIC_SHORT_FLAG (1 << 1)
#else
#define _UATOMIC_HAS_ATOMIC_SHORT_FLAG (0)
#endif

#ifdef UATOMIC_HAS_ATOMIC_INT
#define _UATOMIC_HAS_ATOMIC_INT_FLAG (1 << 2)
#else
#define _UATOMIC_HAS_ATOMIC_INT_FLAG (0)
#endif

#ifdef UATOMIC_HAS_ATOMIC_LLONG
#define _UATOMIC_HAS_ATOMIC_LLONG_FLAG (1 << 3)
#else
#define _UATOMIC_HAS_ATOMIC_LLONG_FLAG (0)
#endif

/*
 * Bitmask of the supported atomic sizes for the architecture.
 */
#define _UATOMIC_HAS_ATOMIC_MASK						\
	(_UATOMIC_HAS_ATOMIC_BYTE_FLAG | _UATOMIC_HAS_ATOMIC_SHORT_FLAG |	\
	 _UATOMIC_HAS_ATOMIC_INT_FLAG | _UATOMIC_HAS_ATOMIC_LLONG_FLAG)

#define _uatomic_has_atomic_type(len)						\
	(len && !(len & (len - 1)) && (_UATOMIC_HAS_ATOMIC_MASK & len))

/*
 * Static assert to test that atomic operations are supported on types of 'len'
 * bytes on the current architecture. The 'len' parameter must be a constant
 * expression.
 */
#define _uatomic_static_assert_atomic(len)					\
	urcu_static_assert(_uatomic_has_atomic_type(len),			\
		"The architecture does not support atomic "			\
		"operations on types of " _uatomic_xstr(len) " bytes.",		\
		uatomic_atomic_type_not_supported)

#ifdef __cplusplus
}
#endif

#endif /* _URCU_ARCH_UATOMIC_UASSERT_H */
