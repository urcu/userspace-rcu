// SPDX-FileCopyrightText: 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
//
// SPDX-License-Identifier: LGPL-2.1-or-later

#ifndef _URCU_COMPILER_H
#define _URCU_COMPILER_H

/*
 * Compiler definitions.
 */

#include <stddef.h>	/* for offsetof */

#if defined __cplusplus
# include <type_traits>	/* for std::remove_cv */
#endif

#include <urcu/config.h>

/*
 * URCU_GCC_VERSION is used to blacklist specific GCC versions with known
 * bugs, clang also defines these macros to an equivalent GCC version it
 * claims to support, so exclude it.
 */
#if defined(__GNUC__) && !defined(__clang__)
# define URCU_GCC_VERSION	(__GNUC__ * 10000 \
				+ __GNUC_MINOR__ * 100 \
				+ __GNUC_PATCHLEVEL__)
#endif

#define caa_likely(x)	__builtin_expect(!!(x), 1)
#define caa_unlikely(x)	__builtin_expect(!!(x), 0)

#ifdef CONFIG_RCU_USE_ATOMIC_BUILTINS
#  define cmm_barrier() __atomic_signal_fence(__ATOMIC_SEQ_CST)
#else
#  define cmm_barrier() __asm__ __volatile__ ("" : : : "memory")
#endif

/*
 * Instruct the compiler to perform only a single access to a variable
 * (prohibits merging and refetching). The compiler is also forbidden to reorder
 * successive instances of CMM_ACCESS_ONCE(), but only when the compiler is aware of
 * particular ordering. Compiler ordering can be ensured, for example, by
 * putting two CMM_ACCESS_ONCE() in separate C statements.
 *
 * This macro does absolutely -nothing- to prevent the CPU from reordering,
 * merging, or refetching absolutely anything at any time.  Its main intended
 * use is to mediate communication between process-level code and irq/NMI
 * handlers, all running on the same CPU.
 */
#define CMM_ACCESS_ONCE(x)	(*(__volatile__  __typeof__(x) *)&(x))

/*
 * If the toolchain support the C11 memory model, define the private macro
 * _CMM_TOOLCHAIN_SUPPORT_C11_MM.
 */
#if ((defined (__cplusplus) && __cplusplus >= 201103L) ||		\
	(defined (__STDC_VERSION__) && __STDC_VERSION__ >= 201112L))
# define _CMM_TOOLCHAIN_SUPPORT_C11_MM
#elif defined(CONFIG_RCU_USE_ATOMIC_BUILTINS)
#  error "URCU was configured to use atomic builtins, but this toolchain does not support them."
#endif

#ifdef _CMM_TOOLCHAIN_SUPPORT_C11_MM
# if defined (__cplusplus) && \
	defined(URCU_GCC_VERSION) && (URCU_GCC_VERSION < 50100)
/*
 * Prior to GCC g++ 5.1 the builtin __atomic_always_lock_free() does not
 * evaluate to a constant expression even if it is documented as such. To keep
 * support for those older compilers, skip the check.
 */
#  define _cmm_static_assert__atomic_lf(size)
# else
/*
 * Fail at compile time if an atomic operation is attempted on an unsupported
 * type for the current architecture.
 */
#  define _cmm_static_assert__atomic_lf(size)					\
	urcu_static_assert(__atomic_always_lock_free(size, 0),			\
			"The architecture does not support atomic lock-free "	\
			"operations on this type.",				\
			_atomic_builtin_type_not_lock_free)
# endif
#endif

/* Make the optimizer believe the variable can be manipulated arbitrarily. */
#define _CMM_OPTIMIZER_HIDE_VAR(var)		\
	__asm__ ("" : "+r" (var))

#ifndef caa_max
#define caa_max(a,b) ((a)>(b)?(a):(b))
#endif

#ifndef caa_min
#define caa_min(a,b) ((a)<(b)?(a):(b))
#endif

#define __CAA_COMBINE_TOKENS(prefix, counter) prefix ## counter
#define CAA_COMBINE_TOKENS(prefix, counter)   __CAA_COMBINE_TOKENS(prefix, counter)

#if defined(__SIZEOF_LONG__)
#define CAA_BITS_PER_LONG	(__SIZEOF_LONG__ * 8)
#elif defined(_LP64)
#define CAA_BITS_PER_LONG	64
#else
#define CAA_BITS_PER_LONG	32
#endif

/*
 * caa_container_of - Get the address of an object containing a field.
 *
 * @ptr: pointer to the field.
 * @type: type of the object.
 * @member: name of the field within the object.
 */
#define caa_container_of(ptr, type, member)				\
	__extension__							\
	({								\
		const __typeof__(((type *) NULL)->member) * __ptr = (ptr); \
		(type *)((char *)__ptr - offsetof(type, member));	\
	})

/*
 * caa_container_of_check_null - Get the address of an object containing a field.
 *
 * @ptr: pointer to the field.
 * @type: type of the object.
 * @member: name of the field within the object.
 *
 * Return the address of the object containing the field. Return NULL if
 * @ptr is NULL.
 */
#define caa_container_of_check_null(ptr, type, member)			\
	__extension__							\
	({								\
		const __typeof__(((type *) NULL)->member) * __ptr = (ptr); \
		(__ptr) ? (type *)((char *)__ptr - offsetof(type, member)) : NULL; \
	})

#define CAA_BUILD_BUG_ON_ZERO(cond) (sizeof(struct { int:-!!(cond); }))
#define CAA_BUILD_BUG_ON(cond) ((void)CAA_BUILD_BUG_ON_ZERO(cond))

/*
 * __rcu is an annotation that documents RCU pointer accesses that need
 * to be protected by a read-side critical section. Eventually, a static
 * checker will be able to use this annotation to detect incorrect RCU
 * usage.
 */
#define __rcu

#ifdef __cplusplus
#define URCU_FORCE_CAST(_type, arg)	(reinterpret_cast<typename std::remove_cv<_type>::type>(arg))
#else
#define URCU_FORCE_CAST(type, arg)	((type) (arg))
#endif

#define caa_is_signed_type(type)	((type) -1 < (type) 0)

/*
 * Cast to unsigned long, sign-extending if @v is signed.
 * Note: casting to a larger type or to same type size keeps the sign of
 * the expression being cast (see C99 6.3.1.3).
 */
#define caa_cast_long_keep_sign(v)	((unsigned long) (v))

#if defined (__GNUC__) \
	&& ((__GNUC__ == 4) && (__GNUC_MINOR__ >= 5)	\
		|| __GNUC__ >= 5)
#define CDS_DEPRECATED(msg)	\
	__attribute__((__deprecated__(msg)))
#else
#define CDS_DEPRECATED(msg)	\
	__attribute__((__deprecated__))
#endif

#define CAA_ARRAY_SIZE(x)	(sizeof(x) / sizeof((x)[0]))

/*
 * Allow user to manually define CMM_SANITIZE_THREAD if their toolchain is not
 * supported by this check.
 */
#ifndef CMM_SANITIZE_THREAD
# if defined(__GNUC__) && defined(__SANITIZE_THREAD__)
#  define CMM_SANITIZE_THREAD
# elif defined(__clang__) && defined(__has_feature)
#  if __has_feature(thread_sanitizer)
#   define CMM_SANITIZE_THREAD
#  endif
# endif
#endif	/* !CMM_SANITIZE_THREAD */

/*
 * Helper to add the volatile qualifier to a pointer.
 *
 * This is used to enforce volatile accesses even when using atomic
 * builtins. Indeed, C11 atomic operations all work on volatile memory
 * accesses, but this is not documented for compiler atomic builtins.
 *
 * This could prevent certain classes of optimization from the compiler such
 * as load/store fusing.
 */
#if defined __cplusplus
template <typename T>
volatile T cmm_cast_volatile(T t)
{
    return static_cast<volatile T>(t);
}
#else
#  define cmm_cast_volatile(ptr)			\
	__extension__					\
	({						\
		(volatile __typeof__(ptr))(ptr);	\
	})
#endif

/*
 * Compile time assertion.
 * - predicate: boolean expression to evaluate,
 * - msg: string to print to the user on failure when `static_assert()` is
 *   supported,
 * - c_identifier_msg: message to be included in the typedef to emulate a
 *   static assertion. This parameter must be a valid C identifier as it will
 *   be used as a typedef name.
 */
#if (defined(__cplusplus) && (defined(__clang__) || (defined(URCU_GCC_VERSION) && URCU_GCC_VERSION >= 70100)))
#define urcu_static_assert(predicate, msg, c_identifier_msg)  \
	static_assert(predicate, msg)
#elif !defined(__cplusplus) && defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 201112L)
#define urcu_static_assert(predicate, msg, c_identifier_msg)  \
	_Static_assert(predicate, msg)
#else
/*
 * Evaluates the predicate and emit a compilation error on failure.
 *
 * If the predicate evaluates to true, this macro defines a struct containing
 * a bitfield of one bit resulting in a successful compilation.
 *
 * If the predicate evaluates to false, this macro defines a struct containing
 * a bitfield of zero bit resulting in a compilation error.
 */
#define urcu_static_assert(predicate, msg, c_identifier_msg)  \
	struct CAA_COMBINE_TOKENS(urcu_assert_, __COUNTER__) \
		{ int c_identifier_msg: !!(predicate); }
#endif

#endif /* _URCU_COMPILER_H */
