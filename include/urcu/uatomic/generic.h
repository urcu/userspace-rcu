// SPDX-FileCopyrightText: 1991-1994 by Xerox Corporation.  All rights reserved.
// SPDX-FileCopyrightText: 1996-1999 by Silicon Graphics.  All rights reserved.
// SPDX-FileCopyrightText: 1999-2004 Hewlett-Packard Development Company, L.P.
// SPDX-FileCopyrightText: 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
// SPDX-FileCopyrightText: 2010 Paolo Bonzini
//
// SPDX-License-Identifier: LicenseRef-Boehm-GC

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

#ifdef __cplusplus
extern "C" {
#endif

#ifndef uatomic_set
#define uatomic_set(addr, v)	((void) CMM_STORE_SHARED(*(addr), (v)))
#endif

#define uatomic_load_store_return_op(op, addr, v, mo)			\
	__extension__							\
	({								\
									\
		switch (mo) {						\
		case CMM_ACQUIRE:					\
		case CMM_CONSUME:					\
		case CMM_RELAXED:					\
			break;						\
		case CMM_RELEASE:					\
		case CMM_ACQ_REL:					\
		case CMM_SEQ_CST:					\
		case CMM_SEQ_CST_FENCE:					\
			cmm_smp_mb();					\
			break;						\
		default:						\
			abort();					\
		}							\
									\
		__typeof__((*addr)) _value = op(addr, v);		\
									\
		switch (mo) {						\
		case CMM_CONSUME:					\
			cmm_smp_read_barrier_depends();			\
			break;						\
		case CMM_ACQUIRE:					\
		case CMM_ACQ_REL:					\
		case CMM_SEQ_CST:					\
		case CMM_SEQ_CST_FENCE:					\
			cmm_smp_mb();					\
			break;						\
		case CMM_RELAXED:					\
		case CMM_RELEASE:					\
			break;						\
		default:						\
			abort();					\
		}							\
		_value;							\
	})

#define uatomic_load_store_op(op, addr, v, mo)				\
	do {								\
		switch (mo) {						\
		case CMM_ACQUIRE:					\
		case CMM_CONSUME:					\
		case CMM_RELAXED:					\
			break;						\
		case CMM_RELEASE:					\
		case CMM_ACQ_REL:					\
		case CMM_SEQ_CST:					\
		case CMM_SEQ_CST_FENCE:					\
			cmm_smp_mb();					\
			break;						\
		default:						\
			abort();					\
		}							\
									\
		op(addr, v);						\
									\
		switch (mo) {						\
		case CMM_CONSUME:					\
			cmm_smp_read_barrier_depends();			\
			break;						\
		case CMM_ACQUIRE:					\
		case CMM_ACQ_REL:					\
		case CMM_SEQ_CST:					\
		case CMM_SEQ_CST_FENCE:					\
			cmm_smp_mb();					\
			break;						\
		case CMM_RELAXED:					\
		case CMM_RELEASE:					\
			break;						\
		default:						\
			abort();					\
		}							\
	} while (0)

#define uatomic_store(addr, v, mo)			\
	do {						\
		switch (mo) {				\
		case CMM_RELAXED:			\
			break;				\
		case CMM_RELEASE:			\
		case CMM_SEQ_CST:			\
		case CMM_SEQ_CST_FENCE:			\
			cmm_smp_mb();			\
			break;				\
		default:				\
			abort();			\
		}					\
							\
		uatomic_set(addr, v);			\
							\
		switch (mo) {				\
		case CMM_RELAXED:			\
		case CMM_RELEASE:			\
			break;				\
		case CMM_SEQ_CST:			\
		case CMM_SEQ_CST_FENCE:			\
			cmm_smp_mb();			\
			break;				\
		default:				\
			abort();			\
		}					\
	} while (0)

#define uatomic_and_mo(addr, v, mo)				\
	uatomic_load_store_op(uatomic_and, addr, v, mo)

#define uatomic_or_mo(addr, v, mo)				\
	uatomic_load_store_op(uatomic_or, addr, v, mo)

#define uatomic_add_mo(addr, v, mo)				\
	uatomic_load_store_op(uatomic_add, addr, v, mo)

#define uatomic_sub_mo(addr, v, mo)				\
	uatomic_load_store_op(uatomic_sub, addr, v, mo)

#define uatomic_inc_mo(addr, mo)				\
	uatomic_load_store_op(uatomic_add, addr, 1, mo)

#define uatomic_dec_mo(addr, mo)				\
	uatomic_load_store_op(uatomic_add, addr, -1, mo)
/*
 * NOTE: We can not just do switch (_value == (old) ? mos : mof) otherwise the
 * compiler emit a -Wduplicated-cond warning.
 */
#define uatomic_cmpxchg_mo(addr, old, new, mos, mof)			\
	__extension__							\
	({								\
		switch (mos) {						\
		case CMM_ACQUIRE:					\
		case CMM_CONSUME:					\
		case CMM_RELAXED:					\
			break;						\
		case CMM_RELEASE:					\
		case CMM_ACQ_REL:					\
		case CMM_SEQ_CST:					\
		case CMM_SEQ_CST_FENCE:					\
			cmm_smp_mb();					\
			break;						\
		default:						\
			abort();					\
		}							\
									\
		__typeof__(*(addr)) _value = uatomic_cmpxchg(addr, old,	\
							new);		\
									\
		if (_value == (old)) {					\
			switch (mos) {					\
			case CMM_CONSUME:				\
				cmm_smp_read_barrier_depends();		\
				break;					\
			case CMM_ACQUIRE:				\
			case CMM_ACQ_REL:				\
			case CMM_SEQ_CST:				\
			case CMM_SEQ_CST_FENCE:				\
				cmm_smp_mb();				\
				break;					\
			case CMM_RELAXED:				\
			case CMM_RELEASE:				\
				break;					\
			default:					\
				abort();				\
			}						\
		} else {						\
			switch (mof) {					\
			case CMM_CONSUME:				\
				cmm_smp_read_barrier_depends();		\
				break;					\
			case CMM_ACQUIRE:				\
			case CMM_ACQ_REL:				\
			case CMM_SEQ_CST:				\
			case CMM_SEQ_CST_FENCE:				\
				cmm_smp_mb();				\
				break;					\
			case CMM_RELAXED:				\
			case CMM_RELEASE:				\
				break;					\
			default:					\
				abort();				\
			}						\
		}							\
		_value;							\
	})

#define uatomic_xchg_mo(addr, v, mo)				\
	uatomic_load_store_return_op(uatomic_xchg, addr, v, mo)

#define uatomic_add_return_mo(addr, v, mo)				\
	uatomic_load_store_return_op(uatomic_add_return, addr, v)

#define uatomic_sub_return_mo(addr, v, mo)				\
	uatomic_load_store_return_op(uatomic_sub_return, addr, v)


#ifndef uatomic_read
#define uatomic_read(addr)	CMM_LOAD_SHARED(*(addr))
#endif

#define uatomic_load(addr, mo)						\
	__extension__							\
	({								\
		switch (mo) {						\
		case CMM_ACQUIRE:					\
		case CMM_CONSUME:					\
		case CMM_RELAXED:					\
			break;						\
		case CMM_SEQ_CST:					\
		case CMM_SEQ_CST_FENCE:					\
			cmm_smp_mb();					\
			break;						\
		default:						\
			abort();					\
		}							\
									\
		__typeof__(*(addr)) _rcu_value = uatomic_read(addr);	\
									\
		switch (mo) {						\
		case CMM_RELAXED:					\
			break;						\
		case CMM_CONSUME:					\
			cmm_smp_read_barrier_depends();			\
			break;						\
		case CMM_ACQUIRE:					\
		case CMM_SEQ_CST:					\
		case CMM_SEQ_CST_FENCE:					\
			cmm_smp_mb();					\
			break;						\
		default:						\
			abort();					\
		}							\
									\
		_rcu_value;						\
	})

#if !defined __OPTIMIZE__  || defined UATOMIC_NO_LINK_ERROR
#ifdef ILLEGAL_INSTR
static inline __attribute__((always_inline))
void _uatomic_link_error(void)
{
	/*
	 * generate an illegal instruction. Cannot catch this with
	 * linker tricks when optimizations are disabled.
	 */
	__asm__ __volatile__(ILLEGAL_INSTR);
}
#else
static inline __attribute__((always_inline, __noreturn__))
void _uatomic_link_error(void)
{
	__builtin_trap();
}
#endif

#else /* #if !defined __OPTIMIZE__  || defined UATOMIC_NO_LINK_ERROR */
extern void _uatomic_link_error(void);
#endif /* #else #if !defined __OPTIMIZE__  || defined UATOMIC_NO_LINK_ERROR */

/* cmpxchg */

#ifndef uatomic_cmpxchg
static inline __attribute__((always_inline))
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
	case 4:
		return __sync_val_compare_and_swap_4((uint32_t *) addr, old,
				_new);
#if (CAA_BITS_PER_LONG == 64)
	case 8:
		return __sync_val_compare_and_swap_8((uint64_t *) addr, old,
				_new);
#endif
	}
	_uatomic_link_error();
	return 0;
}


#define uatomic_cmpxchg(addr, old, _new)				      \
	((__typeof__(*(addr))) _uatomic_cmpxchg((addr),			      \
						caa_cast_long_keep_sign(old), \
						caa_cast_long_keep_sign(_new),\
						sizeof(*(addr))))


/* uatomic_and */

#ifndef uatomic_and
static inline __attribute__((always_inline))
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
	case 4:
		__sync_and_and_fetch_4((uint32_t *) addr, val);
		return;
#if (CAA_BITS_PER_LONG == 64)
	case 8:
		__sync_and_and_fetch_8((uint64_t *) addr, val);
		return;
#endif
	}
	_uatomic_link_error();
}

#define uatomic_and(addr, v)			\
	(_uatomic_and((addr),			\
		caa_cast_long_keep_sign(v),	\
		sizeof(*(addr))))
#define cmm_smp_mb__before_uatomic_and()	cmm_barrier()
#define cmm_smp_mb__after_uatomic_and()		cmm_barrier()

#endif

/* uatomic_or */

#ifndef uatomic_or
static inline __attribute__((always_inline))
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
	case 4:
		__sync_or_and_fetch_4((uint32_t *) addr, val);
		return;
#if (CAA_BITS_PER_LONG == 64)
	case 8:
		__sync_or_and_fetch_8((uint64_t *) addr, val);
		return;
#endif
	}
	_uatomic_link_error();
	return;
}

#define uatomic_or(addr, v)			\
	(_uatomic_or((addr),			\
		caa_cast_long_keep_sign(v),	\
		sizeof(*(addr))))
#define cmm_smp_mb__before_uatomic_or()		cmm_barrier()
#define cmm_smp_mb__after_uatomic_or()		cmm_barrier()

#endif


/* uatomic_add_return */

#ifndef uatomic_add_return
static inline __attribute__((always_inline))
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
	case 4:
		return __sync_add_and_fetch_4((uint32_t *) addr, val);
#if (CAA_BITS_PER_LONG == 64)
	case 8:
		return __sync_add_and_fetch_8((uint64_t *) addr, val);
#endif
	}
	_uatomic_link_error();
	return 0;
}


#define uatomic_add_return(addr, v)					    \
	((__typeof__(*(addr))) _uatomic_add_return((addr),		    \
						caa_cast_long_keep_sign(v), \
						sizeof(*(addr))))
#endif /* #ifndef uatomic_add_return */

#ifndef uatomic_xchg
/* xchg */

static inline __attribute__((always_inline))
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
	case 4:
	{
		uint32_t old;

		do {
			old = uatomic_read((uint32_t *) addr);
		} while (!__sync_bool_compare_and_swap_4((uint32_t *) addr,
				old, val));

		return old;
	}
#if (CAA_BITS_PER_LONG == 64)
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
	_uatomic_link_error();
	return 0;
}

#define uatomic_xchg(addr, v)						    \
	((__typeof__(*(addr))) _uatomic_exchange((addr),		    \
						caa_cast_long_keep_sign(v), \
						sizeof(*(addr))))
#endif /* #ifndef uatomic_xchg */

#else /* #ifndef uatomic_cmpxchg */

#ifndef uatomic_and
/* uatomic_and */

static inline __attribute__((always_inline))
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
#if (CAA_BITS_PER_LONG == 64)
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
	_uatomic_link_error();
}

#define uatomic_and(addr, v)			\
	(_uatomic_and((addr),			\
		caa_cast_long_keep_sign(v),	\
		sizeof(*(addr))))
#define cmm_smp_mb__before_uatomic_and()	cmm_barrier()
#define cmm_smp_mb__after_uatomic_and()		cmm_barrier()

#endif /* #ifndef uatomic_and */

#ifndef uatomic_or
/* uatomic_or */

static inline __attribute__((always_inline))
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
#if (CAA_BITS_PER_LONG == 64)
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
	_uatomic_link_error();
}

#define uatomic_or(addr, v)			\
	(_uatomic_or((addr),			\
		caa_cast_long_keep_sign(v),	\
		sizeof(*(addr))))
#define cmm_smp_mb__before_uatomic_or()		cmm_barrier()
#define cmm_smp_mb__after_uatomic_or()		cmm_barrier()

#endif /* #ifndef uatomic_or */

#ifndef uatomic_add_return
/* uatomic_add_return */

static inline __attribute__((always_inline))
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
#if (CAA_BITS_PER_LONG == 64)
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
	_uatomic_link_error();
	return 0;
}

#define uatomic_add_return(addr, v)					    \
	((__typeof__(*(addr))) _uatomic_add_return((addr),		    \
						caa_cast_long_keep_sign(v), \
						sizeof(*(addr))))
#endif /* #ifndef uatomic_add_return */

#ifndef uatomic_xchg
/* xchg */

static inline __attribute__((always_inline))
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
#if (CAA_BITS_PER_LONG == 64)
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
	_uatomic_link_error();
	return 0;
}

#define uatomic_xchg(addr, v)						    \
	((__typeof__(*(addr))) _uatomic_exchange((addr),		    \
						caa_cast_long_keep_sign(v), \
						sizeof(*(addr))))
#endif /* #ifndef uatomic_xchg */

#endif /* #else #ifndef uatomic_cmpxchg */

/* uatomic_sub_return, uatomic_add, uatomic_sub, uatomic_inc, uatomic_dec */

#ifndef uatomic_add
#define uatomic_add(addr, v)		(void)uatomic_add_return((addr), (v))
#define cmm_smp_mb__before_uatomic_add()	cmm_barrier()
#define cmm_smp_mb__after_uatomic_add()		cmm_barrier()
#endif

#define uatomic_sub_return(addr, v)	\
	uatomic_add_return((addr), -(caa_cast_long_keep_sign(v)))
#define uatomic_sub(addr, v)		\
	uatomic_add((addr), -(caa_cast_long_keep_sign(v)))
#define cmm_smp_mb__before_uatomic_sub()	cmm_smp_mb__before_uatomic_add()
#define cmm_smp_mb__after_uatomic_sub()		cmm_smp_mb__after_uatomic_add()

#ifndef uatomic_inc
#define uatomic_inc(addr)		uatomic_add((addr), 1)
#define cmm_smp_mb__before_uatomic_inc()	cmm_smp_mb__before_uatomic_add()
#define cmm_smp_mb__after_uatomic_inc()		cmm_smp_mb__after_uatomic_add()
#endif

#ifndef uatomic_dec
#define uatomic_dec(addr)		uatomic_add((addr), -1)
#define cmm_smp_mb__before_uatomic_dec()	cmm_smp_mb__before_uatomic_add()
#define cmm_smp_mb__after_uatomic_dec()		cmm_smp_mb__after_uatomic_add()
#endif

#ifdef __cplusplus
}
#endif

#endif /* _URCU_UATOMIC_GENERIC_H */
