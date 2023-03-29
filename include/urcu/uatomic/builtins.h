/*
 * urcu/uatomic/builtins.h
 *
 * Copyright (c) 2023 Olivier Dion <odion@efficios.com>
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

#if defined(__GNUC__)
# define UATOMIC_HAS_ATOMIC_BYTE  __GCC_ATOMIC_CHAR_LOCK_FREE
# define UATOMIC_HAS_ATOMIC_SHORT __GCC_ATOMIC_SHORT_LOCK_FREE
#elif defined(__clang__)
# define UATOMIC_HAS_ATOMIC_BYTE  __CLANG_ATOMIC_CHAR_LOCK_FREE
# define UATOMIC_HAS_ATOMIC_SHORT __CLANG_ATOMIC_SHORT_LOCK_FREE
#else
/* #  define UATOMIC_HAS_ATOMIC_BYTE  */
/* #  define UATOMIC_HAS_ATOMIC_SHORT */
#endif

#include <urcu/uatomic/builtins-generic.h>

#endif	/* _URCU_UATOMIC_BUILTINS_H */
