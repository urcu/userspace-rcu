// SPDX-FileCopyrightText: 1991-1994 by Xerox Corporation.  All rights reserved.
// SPDX-FileCopyrightText: 1996-1999 by Silicon Graphics.  All rights reserved.
// SPDX-FileCopyrightText: 1999-2004 Hewlett-Packard Development Company, L.P.
// SPDX-FileCopyrightText: 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
// SPDX-FileCopyrightText: 2010 Paolo Bonzini
//
// SPDX-License-Identifier: LicenseRef-Boehm-GC

/*
 * Generic uatomic implementation based on GCC __sync built-in functions or the
 * newer __atomic built-ins if the compiler supports C11.
 */

#ifndef _URCU_UATOMIC_GENERIC_H
#define _URCU_UATOMIC_GENERIC_H

/*
 * Code inspired from libuatomic_ops-1.2, inherited in part from the
 * Boehm-Demers-Weiser conservative garbage collector.
 */

#include <stdint.h>
#include <stdlib.h>

#include <urcu/compiler.h>
#include <urcu/system.h>
#include <urcu/uatomic/uassert.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Can be defined for the architecture.
 *
 * What needs to be emitted _before_ the `operation' with memory ordering `mo'.
 */
#ifndef _cmm_compat_c11_smp_mb__before_mo
# define _cmm_compat_c11_smp_mb__before_mo(operation, mo)	\
	do {							\
		switch (mo) {					\
		case CMM_SEQ_CST_FENCE:				\
		case CMM_SEQ_CST:				\
		case CMM_ACQ_REL:				\
		case CMM_RELEASE:				\
			cmm_smp_mb();				\
			break;					\
		case CMM_ACQUIRE:				\
		case CMM_CONSUME:				\
		case CMM_RELAXED:				\
			break;					\
		default:					\
			abort();				\
			break;					\
								\
		}						\
	} while(0)

#endif	/* _cmm_compat_c11_smp_mb__before_mo */

/*
 * Can be defined for the architecture.
 *
 * What needs to be emitted _after_ the `operation' with memory ordering `mo'.
 */
#ifndef _cmm_compat_c11_smp_mb__after_mo
# define _cmm_compat_c11_smp_mb__after_mo(operation, mo)	\
	do {							\
		switch (mo) {					\
		case CMM_SEQ_CST_FENCE:				\
		case CMM_SEQ_CST:				\
		case CMM_ACQUIRE:				\
		case CMM_CONSUME:				\
		case CMM_ACQ_REL:				\
			cmm_smp_mb();				\
			break;					\
		case CMM_RELEASE:				\
		case CMM_RELAXED:				\
			break;					\
		default:					\
			abort();				\
			break;					\
								\
		}						\
	} while(0)
#endif /* _cmm_compat_c11_smp_mb__after_mo */

/*
 * If the toolchain supports the C11 memory model, then it is safe to implement
 * `uatomic_store_mo()' in term of __atomic builtins.  This has the effect of
 * reducing the number of emitted memory barriers except for the
 * CMM_SEQ_CST_FENCE memory order.
 */
#ifndef uatomic_store_mo
#  ifdef _CMM_TOOLCHAIN_SUPPORT_C11_MM
#    define uatomic_store_mo(addr, v, mo)			\
	do {							\
		_cmm_static_assert__atomic_lf(sizeof(*(addr)));	\
		__atomic_store_n(cmm_cast_volatile(addr), v,	\
				cmm_to_c11(mo));		\
		cmm_seq_cst_fence_after_atomic(mo);		\
	} while (0)
#  else
#    define uatomic_store_mo(addr, v, mo)				\
	do {								\
		_uatomic_static_assert_atomic(sizeof(*(addr)));		\
		_cmm_compat_c11_smp_mb__before_mo(uatomic_store, mo);	\
		(void) CMM_STORE_SHARED(*(addr), v);			\
		_cmm_compat_c11_smp_mb__after_mo(uatomic_store, mo);	\
	} while (0)
#  endif  /* _CMM_TOOLCHAIN_SUPPORT_C11_MM */
#endif	/* !uatomic_store */

/*
 * If the toolchain supports the C11 memory model, then it is safe to implement
 * `uatomic_load_mo()' in term of __atomic builtins.  This has the effect of
 * reducing the number of emitted memory barriers except for the
 * CMM_SEQ_CST_FENCE memory order.
 */
#ifndef uatomic_load_mo
#  ifdef _CMM_TOOLCHAIN_SUPPORT_C11_MM
#    define uatomic_load_mo(addr, mo)					\
	__extension__							\
	({								\
		_cmm_static_assert__atomic_lf(sizeof(*(addr)));		\
		__typeof__(*(addr)) _value =				\
			__atomic_load_n(cmm_cast_volatile(addr),	\
					cmm_to_c11(mo));		\
		cmm_seq_cst_fence_after_atomic(mo);			\
									\
		_value;							\
	})
#  else
#    define uatomic_load_mo(addr, mo)					\
	__extension__							\
	({								\
		_uatomic_static_assert_atomic(sizeof(*(addr)));		\
		_cmm_compat_c11_smp_mb__before_mo(uatomic_load, mo);	\
		__typeof__(*(addr)) _rcu_value = CMM_LOAD_SHARED(*(addr)); \
		_cmm_compat_c11_smp_mb__after_mo(uatomic_load, mo);	\
									\
		_rcu_value;						\
	})
#  endif  /* _CMM_TOOLCHAIN_SUPPORT_C11_MM */
#endif	/* !uatomic_load */

/*
 * NOTE: All RMW operations are implemented using the `__sync' builtins.  All
 * builtins used are documented to be considered a "full barrier".  Therefore,
 * for RMW operations, nothing is emitted for any memory order.
 */

/* uatomic_cmpxchg_mo */

#ifndef uatomic_cmpxchg_mo
static inline __attribute__((__always_inline__))
unsigned long _uatomic_cmpxchg(void *addr, unsigned long old,
			      unsigned long _new, int len)
{
	switch (len) {
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	case 1:
		return __sync_val_compare_and_swap_1((uint8_t *) addr, old,
				_new);
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	case 2:
		return __sync_val_compare_and_swap_2((uint16_t *) addr, old,
				_new);
#endif
#ifdef UATOMIC_HAS_ATOMIC_INT
	case 4:
		return __sync_val_compare_and_swap_4((uint32_t *) addr, old,
				_new);
#endif
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
		return __sync_val_compare_and_swap_8((uint64_t *) addr, old,
				_new);
#endif
	}
	return 0;
}

#define uatomic_cmpxchg_mo(addr, old, _new, mos, mof)			\
	__extension__							\
	({								\
		_uatomic_static_assert_atomic(sizeof(*(addr)));		\
		(__typeof__(*(addr))) _uatomic_cmpxchg((addr),		\
					caa_cast_long_keep_sign(old),	\
					caa_cast_long_keep_sign(_new),	\
					sizeof(*(addr)));		\
	})

/* uatomic_and_mo */

#ifndef uatomic_and_mo
static inline __attribute__((__always_inline__))
void _uatomic_and(void *addr, unsigned long val,
		  int len)
{
	switch (len) {
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	case 1:
		__sync_and_and_fetch_1((uint8_t *) addr, val);
		return;
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	case 2:
		__sync_and_and_fetch_2((uint16_t *) addr, val);
		return;
#endif
#ifdef UATOMIC_HAS_ATOMIC_INT
	case 4:
		__sync_and_and_fetch_4((uint32_t *) addr, val);
		return;
#endif
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
		__sync_and_and_fetch_8((uint64_t *) addr, val);
		return;
#endif
	}
}

#define uatomic_and_mo(addr, v, mo)					\
	__extension__							\
	({								\
		_uatomic_static_assert_atomic(sizeof(*(addr)));		\
		_uatomic_and((addr),					\
				caa_cast_long_keep_sign(v),		\
				sizeof(*(addr)));			\
	})

#define cmm_smp_mb__before_uatomic_and()	cmm_barrier()
#define cmm_smp_mb__after_uatomic_and()		cmm_barrier()

#endif

/* uatomic_or_mo */

#ifndef uatomic_or_mo
static inline __attribute__((__always_inline__))
void _uatomic_or(void *addr, unsigned long val,
		 int len)
{
	switch (len) {
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	case 1:
		__sync_or_and_fetch_1((uint8_t *) addr, val);
		return;
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	case 2:
		__sync_or_and_fetch_2((uint16_t *) addr, val);
		return;
#endif
#ifdef UATOMIC_HAS_ATOMIC_INT
	case 4:
		__sync_or_and_fetch_4((uint32_t *) addr, val);
		return;
#endif
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
		__sync_or_and_fetch_8((uint64_t *) addr, val);
		return;
#endif
	}
	return;
}

#define uatomic_or_mo(addr, v, mo)					\
	__extension__							\
	({								\
		_uatomic_static_assert_atomic(sizeof(*(addr)));		\
		_uatomic_or((addr),					\
				caa_cast_long_keep_sign(v),		\
				sizeof(*(addr)));			\
	})

#define cmm_smp_mb__before_uatomic_or()		cmm_barrier()
#define cmm_smp_mb__after_uatomic_or()		cmm_barrier()

#endif


/* uatomic_add_return_mo */

#ifndef uatomic_add_return_mo
static inline __attribute__((__always_inline__))
unsigned long _uatomic_add_return(void *addr, unsigned long val,
				 int len)
{
	switch (len) {
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	case 1:
		return __sync_add_and_fetch_1((uint8_t *) addr, val);
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	case 2:
		return __sync_add_and_fetch_2((uint16_t *) addr, val);
#endif
#ifdef UATOMIC_HAS_ATOMIC_INT
	case 4:
		return __sync_add_and_fetch_4((uint32_t *) addr, val);
#endif
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
		return __sync_add_and_fetch_8((uint64_t *) addr, val);
#endif
	}
	return 0;
}


#define uatomic_add_return_mo(addr, v, mo)				\
	__extension__							\
	({								\
		_uatomic_static_assert_atomic(sizeof(*(addr)));		\
		(__typeof__(*(addr))) _uatomic_add_return((addr),	\
					caa_cast_long_keep_sign(v),	\
					sizeof(*(addr)));		\
	})

#endif /* #ifndef uatomic_add_return */

#ifndef uatomic_xchg_mo
/* xchg */

static inline __attribute__((__always_inline__))
unsigned long _uatomic_exchange(void *addr, unsigned long val, int len)
{
	switch (len) {
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	case 1:
	{
		uint8_t old;

		do {
			old = uatomic_read((uint8_t *) addr);
		} while (!__sync_bool_compare_and_swap_1((uint8_t *) addr,
				old, val));

		return old;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	case 2:
	{
		uint16_t old;

		do {
			old = uatomic_read((uint16_t *) addr);
		} while (!__sync_bool_compare_and_swap_2((uint16_t *) addr,
				old, val));

		return old;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_INT
	case 4:
	{
		uint32_t old;

		do {
			old = uatomic_read((uint32_t *) addr);
		} while (!__sync_bool_compare_and_swap_4((uint32_t *) addr,
				old, val));

		return old;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
	{
		uint64_t old;

		do {
			old = uatomic_read((uint64_t *) addr);
		} while (!__sync_bool_compare_and_swap_8((uint64_t *) addr,
				old, val));

		return old;
	}
#endif
	}
	return 0;
}

#define uatomic_xchg_mo(addr, v, mo)					\
	__extension__							\
	({								\
		_uatomic_static_assert_atomic(sizeof(*(addr)));		\
		(__typeof__(*(addr))) _uatomic_exchange((addr),		\
					caa_cast_long_keep_sign(v),	\
					sizeof(*(addr)));		\
	})

#endif /* #ifndef uatomic_xchg_mo */

#else /* #ifndef uatomic_cmpxchg_mo */

#ifndef uatomic_and_mo
/* uatomic_and_mo */

static inline __attribute__((__always_inline__))
void _uatomic_and(void *addr, unsigned long val, int len)
{
	switch (len) {
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	case 1:
	{
		uint8_t old, oldt;

		oldt = uatomic_read((uint8_t *) addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, old & val, 1);
		} while (oldt != old);

		return;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	case 2:
	{
		uint16_t old, oldt;

		oldt = uatomic_read((uint16_t *) addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, old & val, 2);
		} while (oldt != old);
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_INT
	case 4:
	{
		uint32_t old, oldt;

		oldt = uatomic_read((uint32_t *) addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, old & val, 4);
		} while (oldt != old);

		return;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
	{
		uint64_t old, oldt;

		oldt = uatomic_read((uint64_t *) addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, old & val, 8);
		} while (oldt != old);

		return;
	}
#endif
	}
}

#define uatomic_and_mo(addr, v, mo)					\
	__extension__							\
	({								\
		_uatomic_static_assert_atomic(sizeof(*(addr)));		\
		_uatomic_and((addr),					\
				caa_cast_long_keep_sign(v),		\
				sizeof(*(addr)));			\
	})

#define cmm_smp_mb__before_uatomic_and()	cmm_barrier()
#define cmm_smp_mb__after_uatomic_and()		cmm_barrier()

#endif /* #ifndef uatomic_and_mo */

#ifndef uatomic_or_mo
/* uatomic_or_mo */

static inline __attribute__((__always_inline__))
void _uatomic_or(void *addr, unsigned long val, int len)
{
	switch (len) {
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	case 1:
	{
		uint8_t old, oldt;

		oldt = uatomic_read((uint8_t *) addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, old | val, 1);
		} while (oldt != old);

		return;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	case 2:
	{
		uint16_t old, oldt;

		oldt = uatomic_read((uint16_t *) addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, old | val, 2);
		} while (oldt != old);

		return;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_INT
	case 4:
	{
		uint32_t old, oldt;

		oldt = uatomic_read((uint32_t *) addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, old | val, 4);
		} while (oldt != old);

		return;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
	{
		uint64_t old, oldt;

		oldt = uatomic_read((uint64_t *) addr);
		do {
			old = oldt;
			oldt = _uatomic_cmpxchg(addr, old, old | val, 8);
		} while (oldt != old);

		return;
	}
#endif
	}
}

#define uatomic_or_mo(addr, v, mo)					\
	__extension__							\
	({								\
		_uatomic_static_assert_atomic(sizeof(*(addr)));		\
		_uatomic_or((addr),					\
				caa_cast_long_keep_sign(v),		\
				sizeof(*(addr)));			\
	})

#define cmm_smp_mb__before_uatomic_or()		cmm_barrier()
#define cmm_smp_mb__after_uatomic_or()		cmm_barrier()

#endif /* #ifndef uatomic_or_mo */

#ifndef uatomic_add_return_mo
/* uatomic_add_return_mo */

static inline __attribute__((__always_inline__))
unsigned long _uatomic_add_return(void *addr, unsigned long val, int len)
{
	switch (len) {
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	case 1:
	{
		uint8_t old, oldt;

		oldt = uatomic_read((uint8_t *) addr);
		do {
			old = oldt;
			oldt = uatomic_cmpxchg((uint8_t *) addr,
                                               old, old + val);
		} while (oldt != old);

		return old + val;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	case 2:
	{
		uint16_t old, oldt;

		oldt = uatomic_read((uint16_t *) addr);
		do {
			old = oldt;
			oldt = uatomic_cmpxchg((uint16_t *) addr,
                                               old, old + val);
		} while (oldt != old);

		return old + val;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_INT
	case 4:
	{
		uint32_t old, oldt;

		oldt = uatomic_read((uint32_t *) addr);
		do {
			old = oldt;
			oldt = uatomic_cmpxchg((uint32_t *) addr,
                                               old, old + val);
		} while (oldt != old);

		return old + val;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
	{
		uint64_t old, oldt;

		oldt = uatomic_read((uint64_t *) addr);
		do {
			old = oldt;
			oldt = uatomic_cmpxchg((uint64_t *) addr,
                                               old, old + val);
		} while (oldt != old);

		return old + val;
	}
#endif
	}
	return 0;
}

#define uatomic_add_return_mo(addr, v, mo)				\
	__extension__							\
	({								\
		_uatomic_static_assert_atomic(sizeof(*(addr)));		\
		(__typeof__(*(addr))) _uatomic_add_return((addr),	\
					caa_cast_long_keep_sign(v),	\
					sizeof(*(addr)));		\
	 })

#endif /* #ifndef uatomic_add_return_mo */

#ifndef uatomic_xchg_mo
/* uatomic_xchg_mo */

static inline __attribute__((__always_inline__))
unsigned long _uatomic_exchange(void *addr, unsigned long val, int len)
{
	switch (len) {
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	case 1:
	{
		uint8_t old, oldt;

		oldt = uatomic_read((uint8_t *) addr);
		do {
			old = oldt;
			oldt = uatomic_cmpxchg((uint8_t *) addr,
                                               old, val);
		} while (oldt != old);

		return old;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	case 2:
	{
		uint16_t old, oldt;

		oldt = uatomic_read((uint16_t *) addr);
		do {
			old = oldt;
			oldt = uatomic_cmpxchg((uint16_t *) addr,
                                               old, val);
		} while (oldt != old);

		return old;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_INT
	case 4:
	{
		uint32_t old, oldt;

		oldt = uatomic_read((uint32_t *) addr);
		do {
			old = oldt;
			oldt = uatomic_cmpxchg((uint32_t *) addr,
                                               old, val);
		} while (oldt != old);

		return old;
	}
#endif
#ifdef UATOMIC_HAS_ATOMIC_LLONG
	case 8:
	{
		uint64_t old, oldt;

		oldt = uatomic_read((uint64_t *) addr);
		do {
			old = oldt;
			oldt = uatomic_cmpxchg((uint64_t *) addr,
                                               old, val);
		} while (oldt != old);

		return old;
	}
#endif
	}
	return 0;
}

#define uatomic_xchg_mo(addr, v, mo)					\
	__extension__							\
	({								\
		_uatomic_static_assert_atomic(sizeof(*(addr)));		\
		(__typeof__(*(addr))) _uatomic_exchange((addr),		\
					caa_cast_long_keep_sign(v), 	\
					sizeof(*(addr)));		\
	})

#endif /* #ifndef uatomic_xchg_mo */

#endif /* #else #ifndef uatomic_cmpxchg_mo */

/* uatomic_sub_return_mo, uatomic_add_mo, uatomic_sub_mo, uatomic_inc_mo, uatomic_dec_mo */

#ifndef uatomic_add_mo
#define uatomic_add_mo(addr, v, mo)		(void)uatomic_add_return_mo((addr), (v), mo)
#define cmm_smp_mb__before_uatomic_add()	cmm_barrier()
#define cmm_smp_mb__after_uatomic_add()		cmm_barrier()
#endif

#define uatomic_sub_return_mo(addr, v, mo)				\
	uatomic_add_return_mo((addr), -(caa_cast_long_keep_sign(v)), mo)
#define uatomic_sub_mo(addr, v, mo)					\
	uatomic_add_mo((addr), -(caa_cast_long_keep_sign(v)), mo)
#define cmm_smp_mb__before_uatomic_sub()	cmm_smp_mb__before_uatomic_add()
#define cmm_smp_mb__after_uatomic_sub()		cmm_smp_mb__after_uatomic_add()

#ifndef uatomic_inc_mo
#define uatomic_inc_mo(addr, mo)		uatomic_add_mo((addr), 1, mo)
#define cmm_smp_mb__before_uatomic_inc()	cmm_smp_mb__before_uatomic_add()
#define cmm_smp_mb__after_uatomic_inc()		cmm_smp_mb__after_uatomic_add()
#endif

#ifndef uatomic_dec_mo
#define uatomic_dec_mo(addr, mo)		uatomic_add((addr), -1, mo)
#define cmm_smp_mb__before_uatomic_dec()	cmm_smp_mb__before_uatomic_add()
#define cmm_smp_mb__after_uatomic_dec()		cmm_smp_mb__after_uatomic_add()
#endif

#ifdef __cplusplus
}
#endif

#endif /* _URCU_UATOMIC_GENERIC_H */
