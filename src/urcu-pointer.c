
/*
 * urcu-pointer.c
 *
 * library wrappers to be used by non-LGPL compatible source code.
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
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
 *
 * IBM's contributions to this file may be relicensed under LGPLv2 or later.
 */

#include <urcu/uatomic.h>

#include <urcu/static/pointer.h>
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include <urcu/pointer.h>

extern void synchronize_rcu(void);

/*
 * This wrapper receives the RCU-protected pointer by *value*: the load of
 * the pointer therefore already happened in the caller as a plain
 * (non-atomic) access, before this function is even entered. As a result
 * the compiler may have broken the address dependency between the pointer
 * load and its later dereference (e.g. through value speculation, or LTO
 * inlining of this trivial wrapper), which lets a weakly-ordered CPU
 * reorder the dependent access ahead of the pointer load and observe
 * pre-publication data, defeating the memory_order_consume guarantee of
 * rcu_dereference().
 *
 * Issue a full barrier to order the caller's pointer load (sequenced
 * before this call) before any dependent access performed after this
 * function returns, restoring the publication ordering regardless of
 * whether the dependency survived. This is unneeded on x86 (TSO): the
 * hardware preserves load-to-load and load-to-store ordering, so the
 * pointer load is already ordered before any dependent access, and the
 * bug cannot manifest. (TSO permits only store-to-load reordering, which
 * is irrelevant here since the pointer access is a load.) Elide the
 * barrier there to avoid penalising the common case.
 */
void *rcu_dereference_sym(void *p)
{
#ifndef URCU_ARCH_X86
	cmm_smp_mb();
#endif
	return p;
}

void *rcu_set_pointer_sym(void **p, void *v)
{
	cmm_wmb();
	uatomic_set(p, v);
	return v;
}

void *rcu_xchg_pointer_sym(void **p, void *v)
{
	cmm_wmb();
	return uatomic_xchg(p, v);
}

void *rcu_cmpxchg_pointer_sym(void **p, void *old, void *_new)
{
	cmm_wmb();
	return uatomic_cmpxchg(p, old, _new);
}
