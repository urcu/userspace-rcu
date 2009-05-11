#ifndef _URCU_H
#define _URCU_H

/*
 * urcu.h
 *
 * Userspace RCU header
 *
 * Copyright February 2009 - Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
 *
 * Credits for Paul E. McKenney <paulmck@linux.vnet.ibm.com>
 * for inspiration coming from the Linux kernel RCU and rcu-preempt.
 *
 * LGPL-compatible code should include this header with :
 *
 * #define _LGPL_SOURCE
 * #include <urcu.h>
 *
 * Distributed under LGPLv2.1
 *
 * IBM's contributions to this file may be relicensed under LGPLv2 or later.
 */

#include <stdlib.h>
#include <pthread.h>

#ifdef _LGPL_SOURCE

#include <urcu-static.h>

/*
 * Mappings for static use of the userspace RCU library.
 * Should only be used in LGPL-compatible code.
 */

#define rcu_dereference		_rcu_dereference
#define rcu_read_lock		_rcu_read_lock
#define rcu_read_unlock		_rcu_read_unlock

#define rcu_assign_pointer	_rcu_assign_pointer
#define rcu_xchg_pointer	_rcu_xchg_pointer
#define rcu_publish_content	_rcu_publish_content

#else /* !_LGPL_SOURCE */

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

extern void rcu_read_lock(void);
extern void rcu_read_unlock(void);

extern void *rcu_dereference(void *p);

extern void *rcu_assign_pointer_sym(void **p, void *v);

#define rcu_assign_pointer(p, v)			\
	rcu_assign_pointer_sym((void **)(p), (v))

extern void *rcu_xchg_pointer_sym(void **p, void *v);
#define rcu_xchg_pointer(p, v)				\
	rcu_xchg_pointer_sym((void **)(p), (v))

extern void *rcu_publish_content_sym(void **p, void *v);
#define rcu_publish_content(p, v)			\
	rcu_publish_content_sym((void **)(p), (v))

#endif /* !_LGPL_SOURCE */

extern void synchronize_rcu(void);

/*
 * Reader thread registration.
 */
extern void rcu_register_thread(void);
extern void rcu_unregister_thread(void);

#endif /* _URCU_H */
