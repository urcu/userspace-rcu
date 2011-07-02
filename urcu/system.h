#ifndef _URCU_SYSTEM_H
#define _URCU_SYSTEM_H

/*
 * system.h
 *
 * System definitions.
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 *
 * THIS MATERIAL IS PROVIDED AS IS, WITH ABSOLUTELY NO WARRANTY EXPRESSED
 * OR IMPLIED.  ANY USE IS AT YOUR OWN RISK.
 *
 * Permission is hereby granted to use or copy this program
 * for any purpose,  provided the above notices are retained on all copies.
 * Permission to modify the code and to distribute modified code is granted,
 * provided the above notices are retained, and a notice that the code was
 * modified is included with the above copyright notice.
 */

#include <urcu/compiler.h>
#include <urcu/arch.h>

/*
 * Identify a shared load. A cmm_smp_rmc() or cmm_smp_mc() should come before the load.
 */
#define _CMM_LOAD_SHARED(p)	       CMM_ACCESS_ONCE(p)

/*
 * Load a data from shared memory, doing a cache flush if required.
 */
#define CMM_LOAD_SHARED(p)			\
	({				\
		cmm_smp_rmc();		\
		_CMM_LOAD_SHARED(p);	\
	})

/*
 * Identify a shared store. A cmm_smp_wmc() or cmm_smp_mc() should follow the store.
 */
#define _CMM_STORE_SHARED(x, v)	({ CMM_ACCESS_ONCE(x) = (v); })

/*
 * Store v into x, where x is located in shared memory. Performs the required
 * cache flush after writing. Returns v.
 */
#define CMM_STORE_SHARED(x, v)		\
	({				\
		typeof(x) _v = _CMM_STORE_SHARED(x, v);	\
		cmm_smp_wmc();		\
		_v;			\
	})

#endif /* _URCU_SYSTEM_H */
