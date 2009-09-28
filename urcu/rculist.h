#ifndef _KCOMPAT_RCULIST_H
#define _KCOMPAT_RCULIST_H

/*
 * RCU-protected list version
 *
 * 2002-10-18 19:01:25-07:00, dipankar@in.ibm.com
 *  [PATCH] RCU helper patchset 2/2
 *
 *  This adds a set of list macros that make handling of list protected
 *  by RCU simpler. The interfaces added are -
 *
 *  list_add_rcu
 *  list_add_tail_rcu
 *        - Adds an element by taking care of memory barrier (wmb()).
 *
 *  list_del_rcu
 *        - Deletes an element but doesn't re-initialize the pointers in
 *          the element for supporting RCU based traversal.
 *
 *  list_for_each_rcu
 *  __list_for_each_rcu
 *        - Traversal of RCU protected list - takes care of memory barriers
 *          transparently.
 *
 */

#define _LGPL_SOURCE
#include <urcu.h>
#include <kcompat/list.h>

/*
 * Insert a new entry between two known consecutive entries.
 *
 * This is only for internal list manipulation where we know
 * the prev/next entries already!
 */
static __inline__ void __list_add_rcu(struct list_head * new,
				      struct list_head * prev,
				      struct list_head * next)
{
	new->next = next;
	new->prev = prev;
	smp_wmb();
	next->prev = new;
	prev->next = new;
}

/**
 * list_add_rcu - add a new entry to rcu-protected list
 * @new: new entry to be added
 * @head: list head to add it after
 *
 * Insert a new entry after the specified head.
 * This is good for implementing stacks.
 *
 * The caller must take whatever precautions are necessary
 * (such as holding appropriate locks) to avoid racing
 * with another list-mutation primitive, such as list_add_rcu()
 * or list_del_rcu(), running on this same list.
 * However, it is perfectly legal to run concurrently with
 * the _rcu list-traversal primitives, such as
 * list_for_each_entry_rcu().
 */
static __inline__ void list_add_rcu(struct list_head *new,
				    struct list_head *head)
{
	__list_add_rcu(new, head, head->next);
}

/**
 * list_add_tail_rcu - add a new entry to rcu-protected list
 * @new: new entry to be added
 * @head: list head to add it before
 *
 * Insert a new entry before the specified head.
 * This is useful for implementing queues.
 *
 * The caller must take whatever precautions are necessary
 * (such as holding appropriate locks) to avoid racing
 * with another list-mutation primitive, such as list_add_tail_rcu()
 * or list_del_rcu(), running on this same list.
 * However, it is perfectly legal to run concurrently with
 * the _rcu list-traversal primitives, such as
 * list_for_each_entry_rcu().
 */
static __inline__ void list_add_tail_rcu(struct list_head *new,
					 struct list_head *head)
{
	__list_add_rcu(new, head->prev, head);
}

/**
 * list_del_rcu - deletes entry from list without re-initialization
 * @entry: the element to delete from the list.
 *
 * Note: list_empty on entry does not return true after this,
 * the entry is in an undefined state. It is useful for RCU based
 * lockfree traversal.
 *
 * The caller must take whatever precautions are necessary
 * (such as holding appropriate locks) to avoid racing
 * with another list-mutation primitive, such as list_del_rcu()
 * or list_add_rcu(), running on this same list.
 * However, it is perfectly legal to run concurrently with
 * the _rcu list-traversal primitives, such as
 * list_for_each_entry_rcu().
 *
 * Note that the caller is not permitted to immediately free
 * the newly deleted entry.  Instead, either synchronize_kernel()
 * or call_rcu() must be used to defer freeing until an RCU
 * grace period has elapsed.
 */
static inline void list_del_rcu(struct list_head *entry)
{
	__list_del(entry->prev, entry->next);
}

/**
 * list_for_each_rcu	-	iterate over an rcu-protected list
 * @pos:	the &struct list_head to use as a loop counter.
 * @head:	the head for your list.
 *
 * This list-traversal primitive may safely run concurrently with
 * the _rcu list-mutation primitives such as list_add_rcu()
 * as long as the traversal is guarded by rcu_read_lock().
 */
#define list_for_each_rcu(pos, head)					\
	for (pos = rcu_dereference((head)->next);			\
	     prefetch(pos->next), pos != (head);			\
	     pos = rcu_dereference(pos->next))

#define __list_for_each_rcu(pos, head)					\
	for (pos = rcu_dereference((head)->next);			\
	     pos != (head);						\
	     pos = rcu_dereference(pos->next))

/**
 * list_for_each_entry_rcu - iterate over a rcu-protected list
 * @pos: the struct type pointer to use as a loop counter
 * @head: the head for your list
 * @member: the name of the struct list_head element in your struct type
 *
 * This list-traversal primitive may safely run concurrently with
 * the _rcu list-mutation primitives such as list_add_rcu()
 * as long as the traversal is guarded by rcu_read_lock().
 */
#define list_for_each_entry_rcu(pos, head, member)			\
	for (pos = list_entry(rcu_dereference((head)->next), typeof(*pos), \
			      member);					\
	     prefetch(pos->member.next), &pos->member != (head);	\
	     pos = list_entry(rcu_dereference(pos->member.next),typeof(*pos), \
			      member))

#endif /* _KCOMPAT_RCULIST_H */
