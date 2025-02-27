// SPDX-FileCopyrightText: 2023 Olivier Dion <odion@efficios.com>
//
// SPDX-License-Identifier: LGPL-2.1-or-later

/*
 * urcu/uatomic/builtins.h
 */

#ifndef _URCU_UATOMIC_BUILTINS_H
#define _URCU_UATOMIC_BUILTINS_H

#include <urcu/arch.h>

#if defined(__has_builtin)
# if !__has_builtin(__atomic_store_n)
#  error "Toolchain does not support __atomic_store_n."
# endif
# if !__has_builtin(__atomic_load_n)
#  error "Toolchain does not support __atomic_load_n."
# endif
# if !__has_builtin(__atomic_exchange_n)
#  error "Toolchain does not support __atomic_exchange_n."
# endif
# if !__has_builtin(__atomic_compare_exchange_n)
#  error "Toolchain does not support __atomic_compare_exchange_n."
# endif
# if !__has_builtin(__atomic_add_fetch)
#  error "Toolchain does not support __atomic_add_fetch."
# endif
# if !__has_builtin(__atomic_sub_fetch)
#  error "Toolchain does not support __atomic_sub_fetch."
# endif
# if !__has_builtin(__atomic_or_fetch)
#  error "Toolchain does not support __atomic_or_fetch."
# endif
# if !__has_builtin(__atomic_thread_fence)
#  error "Toolchain does not support __atomic_thread_fence."
# endif
# if !__has_builtin(__atomic_signal_fence)
#  error "Toolchain does not support __atomic_signal_fence."
# endif
#elif defined(__GNUC__)
# define GCC_VERSION (__GNUC__       * 10000 + \
		       __GNUC_MINOR__ * 100   + \
		       __GNUC_PATCHLEVEL__)
# if  GCC_VERSION < 40700
#  error "GCC version is too old. Version must be 4.7 or greater"
# endif
# undef  GCC_VERSION
#else
# error "Toolchain is not supported."
#endif

/*
 * Use the compiler provided defines, a value of '2' means that the atomic
 * operations for the type are always lock free and won't require linking with
 * libatomic.
 */
#if defined(__clang__)
# if __CLANG_ATOMIC_CHAR_LOCK_FREE == 2
#  define UATOMIC_HAS_ATOMIC_BYTE
# endif
# if __CLANG_ATOMIC_SHORT_LOCK_FREE == 2
#  define UATOMIC_HAS_ATOMIC_SHORT
# endif
#elif defined(__GNUC__)
# if __GCC_ATOMIC_CHAR_LOCK_FREE == 2
#  define UATOMIC_HAS_ATOMIC_BYTE
# endif
# if __GCC_ATOMIC_SHORT_LOCK_FREE == 2
#  define UATOMIC_HAS_ATOMIC_SHORT
# endif
#else
# error "Toolchain is missing lock-free atomic defines."
#endif

#include <urcu/uatomic/builtins-generic.h>

#endif	/* _URCU_UATOMIC_BUILTINS_H */
