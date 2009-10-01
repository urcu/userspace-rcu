/* Copyright (C) 2002 Free Software Foundation, Inc.
   This file is part of the GNU C Library.
   Contributed by Ulrich Drepper <drepper@redhat.com>, 2002.

   Copyright (C) 2009 Pierre-Marc Fournier
   Conversion to RCU list.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, write to the Free
   Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
   02111-1307 USA.  */

#ifndef _URCU_RCULIST_H
#define _URCU_RCULIST_H

#include <urcu/list.h>
#include <urcu/arch.h>
#include <urcu-pointer.h>

/* Add new element at the head of the list.
 */
static inline void list_add_rcu(list_t *newp, list_t *head)
{
	newp->next = head->next;
	newp->prev = head;
	smp_wmb();
	head->next->prev = newp;
	head->next = newp;
}


/* Remove element from list. */
static inline void list_del_rcu(list_t *elem)
{
	elem->next->prev = elem->prev;
	elem->prev->next = elem->next;
}


/* Iterate through elements of the list.
 * This must be done while rcu_read_lock() is held.
 */

#define list_for_each_entry_rcu(pos, head, member)				\
	for (pos = list_entry(rcu_dereference((head)->next), typeof(*pos), member);	\
	     &pos->member != (head);					\
	     pos = list_entry(rcu_dereference(pos->member.next), typeof(*pos), member))

#endif	/* _URCU_RCULIST_H */
