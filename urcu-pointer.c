
/*
 * urcu-pointer.c
 *
 * library wrappers to be used by non-LGPL compatible source code.
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
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

#include "urcu-pointer-static.h"
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include "urcu-pointer.h"

extern void synchronize_rcu(void);

void *rcu_dereference_sym(void *p)
{
	return _rcu_dereference(p);
}

void *rcu_set_pointer_sym(void **p, void *v)
{
	wmb();
	return STORE_SHARED(*p, v);
}

void *rcu_xchg_pointer_sym(void **p, void *v)
{
	wmb();
	return uatomic_xchg(p, v);
}

void *rcu_cmpxchg_pointer_sym(void **p, void *old, void *_new)
{
	wmb();
	return uatomic_cmpxchg(p, old, _new);
}
