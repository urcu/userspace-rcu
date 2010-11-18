#ifndef _KCOMPAT_HLIST_H
#define _KCOMPAT_HLIST_H

/*
 * Kernel sourcecode compatible lightweight single pointer list head useful
 * for implementing hash tables
 *
 * Copyright (C) 2009 Novell Inc.
 *
 * Author: Jan Blunck <jblunck@suse.de>
 *
 * Copyright (C) 2010 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License version 2.1 as
 * published by the Free  Software Foundation.
 */

struct cds_hlist_head
{
	struct cds_hlist_node *next;
};

struct cds_hlist_node
{
	struct cds_hlist_node *next;
	struct cds_hlist_node *prev;
};

/* Initialize a new list head.  */
static inline void  CDS_INIT_HLIST_HEAD(struct cds_hlist_head *ptr)
{
	ptr->next = NULL;
}

/* Get typed element from list at a given position.  */
#define cds_hlist_entry(ptr, type, member)					\
	((type *) ((char *) (ptr) - (unsigned long) (&((type *) 0)->member)))

/* Add new element at the head of the list.  */
static inline void cds_hlist_add_head (struct cds_hlist_node *newp,
				   struct cds_hlist_head *head)
{
	if (head->next)
		head->next->prev = newp;

	newp->next = head->next;
	newp->prev = (struct cds_hlist_node *)head;
	head->next = newp;
}

/* Remove element from list.  */
static inline void cds_hlist_del (struct cds_hlist_node *elem)
{
	if (elem->next)
		elem->next->prev = elem->prev;

	elem->prev->next = elem->next;
}

#define cds_hlist_for_each_entry(entry, pos, head, member)			\
	for (pos = (head)->next,					\
		     entry = cds_hlist_entry(pos, typeof(*entry), member);	\
	     pos != NULL;						\
	     pos = pos->next,					\
		     entry = cds_hlist_entry(pos, typeof(*entry), member))

#define cds_hlist_for_each_entry_safe(entry, pos, p, head, member)		\
	for (pos = (head)->next,					\
		     entry = cds_hlist_entry(pos, typeof(*entry), member);	\
	     (pos != NULL) && ({ p = pos->next; 1;});			\
	     pos = p,							\
		     entry = cds_hlist_entry(pos, typeof(*entry), member))

#endif	/* _KCOMPAT_HLIST_H */
