#ifndef _URCU_STATIC_LFSTACK_H
#define _URCU_STATIC_LFSTACK_H

/*
 * urcu/static/lfstack.h
 *
 * Userspace RCU library - Lock-Free Stack
 *
 * Copyright 2010-2012 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 *
 * TO BE INCLUDED ONLY IN LGPL-COMPATIBLE CODE. See rculfstack.h for linking
 * dynamically with the userspace rcu library.
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

#include <urcu/uatomic.h>
#include <urcu-pointer.h>

#ifdef __cplusplus
extern "C" {
#endif

static inline
void _cds_lfs_node_init(struct cds_lfs_node *node)
{
}

static inline
void _cds_lfs_init(struct cds_lfs_stack *s)
{
	s->head = NULL;
}

/*
 * cds_lfs_push: push a node into the stack.
 *
 * Does not require any synchronization with other push nor pop.
 *
 * Lock-free stack push is not subject to ABA problem, so no need to
 * take the RCU read-side lock. Even if "head" changes between two
 * uatomic_cmpxchg() invocations here (being popped, and then pushed
 * again by one or more concurrent threads), the second
 * uatomic_cmpxchg() invocation only cares about pushing a new entry at
 * the head of the stack, ensuring consistency by making sure the new
 * node->next is the same pointer value as the value replaced as head.
 * It does not care about the content of the actual next node, so it can
 * very well be reallocated between the two uatomic_cmpxchg().
 *
 * We take the approach of expecting the stack to be usually empty, so
 * we first try an initial uatomic_cmpxchg() on a NULL old_head, and
 * retry if the old head was non-NULL (the value read by the first
 * uatomic_cmpxchg() is used as old head for the following loop). The
 * upside of this scheme is to minimize the amount of cacheline traffic,
 * always performing an exclusive cacheline access, rather than doing
 * non-exclusive followed by exclusive cacheline access (which would be
 * required if we first read the old head value). This design decision
 * might be revisited after more throrough benchmarking on various
 * platforms.
 *
 * Returns 0 if the stack was empty prior to adding the node.
 * Returns non-zero otherwise.
 */
static inline
int _cds_lfs_push(struct cds_lfs_stack *s,
		  struct cds_lfs_node *node)
{
	struct cds_lfs_node *head = NULL;

	for (;;) {
		struct cds_lfs_node *old_head = head;

		/*
		 * node->next is still private at this point, no need to
		 * perform a _CMM_STORE_SHARED().
		 */
		node->next = head;
		/*
		 * uatomic_cmpxchg() implicit memory barrier orders earlier
		 * stores to node before publication.
		 */
		head = uatomic_cmpxchg(&s->head, old_head, node);
		if (old_head == head)
			break;
	}
	return (int) !!((unsigned long) head);
}

/*
 * cds_lfs_pop: pop a node from the stack.
 *
 * Returns NULL if stack is empty.
 *
 * cds_lfs_pop needs to be synchronized using one of the following
 * techniques:
 *
 * 1) Calling cds_lfs_pop under rcu read lock critical section. The
 *    caller must wait for a grace period to pass before freeing the
 *    returned node or modifying the cds_lfs_node structure.
 * 2) Using mutual exclusion (e.g. mutexes) to protect cds_lfs_pop
 *    callers.
 * 3) Ensuring that only ONE thread can call cds_lfs_pop().
 *    (multi-provider/single-consumer scheme).
 */
static inline
struct cds_lfs_node *_cds_lfs_pop(struct cds_lfs_stack *s)
{
	for (;;) {
		struct cds_lfs_node *head;

		head = _CMM_LOAD_SHARED(s->head);
		if (head) {
			struct cds_lfs_node *next;

			/*
			 * Read head before head->next. Matches the
			 * implicit memory barrier before
			 * uatomic_cmpxchg() in cds_lfs_push.
			 */
			cmm_smp_read_barrier_depends();
			next = _CMM_LOAD_SHARED(head->next);
			if (uatomic_cmpxchg(&s->head, head, next) == head) {
				return head;
			} else {
				/* Concurrent modification. Retry. */
				continue;
			}
		} else {
			/* Empty stack */
			return NULL;
		}
	}
}

#ifdef __cplusplus
}
#endif

#endif /* _URCU_STATIC_LFSTACK_H */
