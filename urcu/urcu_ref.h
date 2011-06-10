#ifndef _URCU_REF_H
#define _URCU_REF_H

/*
 * Userspace RCU - Reference counting
 *
 * Copyright (C) 2009 Novell Inc.
 * Copyright (C) 2010 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 *
 * Author: Jan Blunck <jblunck@suse.de>
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License version 2.1 as
 * published by the Free  Software Foundation.
 */

#include <assert.h>
#include <urcu/uatomic.h>

struct urcu_ref {
	long refcount; /* ATOMIC */
};

static inline void urcu_ref_set(struct urcu_ref *ref, long val)
{
	uatomic_set(&ref->refcount, val);
}

static inline void urcu_ref_init(struct urcu_ref *ref)
{
	urcu_ref_set(ref, 1);
}

static inline void urcu_ref_get(struct urcu_ref *ref)
{
	uatomic_add(&ref->refcount, 1);
}

static inline void urcu_ref_put(struct urcu_ref *ref,
				void (*release)(struct urcu_ref *))
{
	long res = uatomic_sub_return(&ref->refcount, 1);
	assert (res >= 0);
	if (res == 0)
		release(ref);
}

#endif /* _URCU_REF_H */
