/* Copyright (C) 2002 Free Software Foundation, Inc.
   This file is part of the GNU C Library.
   Contributed by Ulrich Drepper <drepper@redhat.com>, 2002.

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

#ifndef _LIST_H
#define _LIST_H	1

/* The definitions of this file are adopted from those which can be
   found in the Linux kernel headers to enable people familiar with
   the latter find their way in these sources as well.  */


/* Basic type for the double-link list.  */
typedef struct cds_list_head
{
  struct cds_list_head *next;
  struct cds_list_head *prev;
} list_t;


/* Define a variable with the head and tail of the list.  */
#define CDS_LIST_HEAD(name) \
  list_t name = { &(name), &(name) }

/* Initialize a new list head.  */
#define CDS_INIT_LIST_HEAD(ptr) \
  (ptr)->next = (ptr)->prev = (ptr)

#define CDS_LIST_HEAD_INIT(name) { .prev = &(name), .next = &(name) }

/* Add new element at the head of the list.  */
static inline void
cds_list_add (list_t *newp, list_t *head)
{
  head->next->prev = newp;
  newp->next = head->next;
  newp->prev = head;
  head->next = newp;
}


/* Add new element at the tail of the list.  */
static inline void
cds_list_add_tail (list_t *newp, list_t *head)
{
  head->prev->next = newp;
  newp->next = head;
  newp->prev = head->prev;
  head->prev = newp;
}


/* Remove element from list.  */
static inline void
__cds_list_del (list_t *prev, list_t *next)
{
  next->prev = prev;
  prev->next = next;
}

/* Remove element from list.  */
static inline void
cds_list_del (list_t *elem)
{
  __cds_list_del (elem->prev, elem->next);
}

/* delete from list, add to another list as head */
static inline void
cds_list_move (list_t *elem, list_t *head)
{
  __cds_list_del (elem->prev, elem->next);
  cds_list_add (elem, head);
}

/* replace an old entry.
 */
static inline void
cds_list_replace(list_t *old, list_t *_new)
{
	_new->next = old->next;
	_new->prev = old->prev;
	_new->prev->next = _new;
	_new->next->prev = _new;
}

/* Join two lists.  */
static inline void
cds_list_splice (list_t *add, list_t *head)
{
  /* Do nothing if the list which gets added is empty.  */
  if (add != add->next)
    {
      add->next->prev = head;
      add->prev->next = head->next;
      head->next->prev = add->prev;
      head->next = add->next;
    }
}


/* Get typed element from list at a given position.  */
#define cds_list_entry(ptr, type, member) \
  ((type *) ((char *) (ptr) - (unsigned long) (&((type *) 0)->member)))



/* Iterate forward over the elements of the list.  */
#define cds_list_for_each(pos, head) \
  for (pos = (head)->next; pos != (head); pos = pos->next)


/* Iterate forward over the elements of the list.  */
#define cds_list_for_each_prev(pos, head) \
  for (pos = (head)->prev; pos != (head); pos = pos->prev)


/* Iterate backwards over the elements list.  The list elements can be
   removed from the list while doing this.  */
#define cds_list_for_each_prev_safe(pos, p, head) \
  for (pos = (head)->prev, p = pos->prev; \
       pos != (head); \
       pos = p, p = pos->prev)

#define cds_list_for_each_entry(pos, head, member)				\
	for (pos = cds_list_entry((head)->next, typeof(*pos), member);	\
	     &pos->member != (head);					\
	     pos = cds_list_entry(pos->member.next, typeof(*pos), member))

#define cds_list_for_each_entry_reverse(pos, head, member)			\
	for (pos = cds_list_entry((head)->prev, typeof(*pos), member);	\
	     &pos->member != (head);					\
	     pos = cds_list_entry(pos->member.prev, typeof(*pos), member))

#define cds_list_for_each_entry_safe(pos, p, head, member)			\
	for (pos = cds_list_entry((head)->next, typeof(*pos), member),	\
		     p = cds_list_entry(pos->member.next,typeof(*pos), member); \
	     &pos->member != (head);					\
	     pos = p, p = cds_list_entry(pos->member.next, typeof(*pos), member))

static inline int cds_list_empty(list_t *head)
{
	return head == head->next;
}

static inline void cds_list_replace_init(list_t *old,
				     list_t *_new)
{
	list_t *head = old->next;
	cds_list_del(old);
	cds_list_add_tail(_new, head);
	CDS_INIT_LIST_HEAD(old);
}

#endif	/* list.h */
