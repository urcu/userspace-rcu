/*
 * urcu/uatomic/builtins-generic.h
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

#ifndef _URCU_UATOMIC_BUILTINS_GENERIC_H
#define _URCU_UATOMIC_BUILTINS_GENERIC_H

#include <urcu/compiler.h>
#include <urcu/system.h>

#define uatomic_store(addr, v, mo)				\
	do {							\
		__atomic_store_n(cmm_cast_volatile(addr), v,	\
				cmm_to_c11(mo));		\
		cmm_seq_cst_fence_after_atomic(mo);		\
	} while (0)

#define uatomic_set(addr, v)				\
	do {						\
		uatomic_store(addr, v, CMM_RELAXED);	\
	} while (0)

#define uatomic_load(addr, mo)						\
	__extension__							\
	({								\
		__typeof__(*(addr)) _value =				\
			__atomic_load_n(cmm_cast_volatile(addr),	\
					cmm_to_c11(mo));		\
		cmm_seq_cst_fence_after_atomic(mo);			\
									\
		_value;							\
	})

#define uatomic_read(addr)			\
	uatomic_load(addr, CMM_RELAXED)

#define uatomic_cmpxchg_mo(addr, old, new, mos, mof)			\
	__extension__							\
	({								\
		__typeof__(*(addr)) _old = (__typeof__(*(addr)))old;	\
									\
		if (__atomic_compare_exchange_n(cmm_cast_volatile(addr), \
							&_old, new, 0,	\
							cmm_to_c11(mos), \
							cmm_to_c11(mof))) { \
			cmm_seq_cst_fence_after_atomic(mos);		\
		} else {						\
			cmm_seq_cst_fence_after_atomic(mof);		\
		}							\
		_old;							\
	})

#define uatomic_cmpxchg(addr, old, new)					\
	uatomic_cmpxchg_mo(addr, old, new, CMM_SEQ_CST_FENCE, CMM_RELAXED)

#define uatomic_xchg_mo(addr, v, mo)					\
	__extension__							\
	({								\
		__typeof__((*addr)) _old =				\
			__atomic_exchange_n(cmm_cast_volatile(addr), v,	\
					cmm_to_c11(mo));		\
		cmm_seq_cst_fence_after_atomic(mo);			\
		_old;							\
	})

#define uatomic_xchg(addr, v)				\
	uatomic_xchg_mo(addr, v, CMM_SEQ_CST_FENCE)

#define uatomic_add_return_mo(addr, v, mo)				\
	__extension__							\
	({								\
		__typeof__(*(addr)) _old =				\
			__atomic_add_fetch(cmm_cast_volatile(addr), v,	\
					cmm_to_c11(mo));		\
		cmm_seq_cst_fence_after_atomic(mo);			\
		_old;							\
	})

#define uatomic_add_return(addr, v)				\
	uatomic_add_return_mo(addr, v, CMM_SEQ_CST_FENCE)

#define uatomic_sub_return_mo(addr, v, mo)				\
	__extension__							\
	({								\
		__typeof__(*(addr)) _old =				\
			__atomic_sub_fetch(cmm_cast_volatile(addr), v,	\
					cmm_to_c11(mo));		\
		cmm_seq_cst_fence_after_atomic(mo);			\
		_old;							\
	})

#define uatomic_sub_return(addr, v)				\
	uatomic_sub_return_mo(addr, v, CMM_SEQ_CST_FENCE)

#define uatomic_and_mo(addr, mask, mo)					\
	do {								\
		(void) __atomic_and_fetch(cmm_cast_volatile(addr), mask, \
					cmm_to_c11(mo));		\
		cmm_seq_cst_fence_after_atomic(mo);			\
	} while (0)

#define uatomic_and(addr, mask)			\
	uatomic_and_mo(addr, mask, CMM_SEQ_CST)

#define uatomic_or_mo(addr, mask, mo)					\
	do {								\
		(void) __atomic_or_fetch(cmm_cast_volatile(addr), mask,	\
					cmm_to_c11(mo));		\
		cmm_seq_cst_fence_after_atomic(mo);			\
	} while (0)


#define uatomic_or(addr, mask)			\
	uatomic_or_mo(addr, mask, CMM_RELAXED)

#define uatomic_add_mo(addr, v, mo)			\
	(void) uatomic_add_return_mo(addr, v, mo)

#define uatomic_add(addr, v)			\
	uatomic_add_mo(addr, v, CMM_RELAXED)

#define uatomic_sub_mo(addr, v, mo)			\
	(void) uatomic_sub_return_mo(addr, v, mo)

#define uatomic_sub(addr, v)			\
	uatomic_sub_mo(addr, v, CMM_RELAXED)

#define uatomic_inc_mo(addr, mo)		\
	uatomic_add_mo(addr, 1, mo)

#define uatomic_inc(addr)			\
	uatomic_inc_mo(addr, CMM_RELAXED)

#define uatomic_dec_mo(addr, mo)		\
	uatomic_sub_mo(addr, 1, mo)

#define uatomic_dec(addr)			\
	uatomic_dec_mo(addr, CMM_RELAXED)

#define cmm_smp_mb__before_uatomic_and() cmm_smp_mb()
#define cmm_smp_mb__after_uatomic_and()  cmm_smp_mb()

#define cmm_smp_mb__before_uatomic_or() cmm_smp_mb()
#define cmm_smp_mb__after_uatomic_or()  cmm_smp_mb()

#define cmm_smp_mb__before_uatomic_add() cmm_smp_mb()
#define cmm_smp_mb__after_uatomic_add()  cmm_smp_mb()

#define cmm_smp_mb__before_uatomic_sub() cmm_smp_mb()
#define cmm_smp_mb__after_uatomic_sub()  cmm_smp_mb()

#define cmm_smp_mb__before_uatomic_inc() cmm_smp_mb()
#define cmm_smp_mb__after_uatomic_inc() cmm_smp_mb()

#define cmm_smp_mb__before_uatomic_dec() cmm_smp_mb()
#define cmm_smp_mb__after_uatomic_dec() cmm_smp_mb()

#endif /* _URCU_UATOMIC_BUILTINS_X86_H */
