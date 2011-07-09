/*
 * rculfhash.c
 *
 * Userspace RCU library - Lock-Free Expandable RCU Hash Table
 *
 * Copyright 2010-2011 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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

#define _LGPL_SOURCE
#include <stdlib.h>
#include <errno.h>
#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include <urcu.h>
#include <urcu-call-rcu.h>
#include <urcu/arch.h>
#include <urcu/uatomic.h>
#include <urcu/jhash.h>
#include <urcu/compiler.h>
#include <urcu/rculfhash.h>
#include <stdio.h>
#include <pthread.h>

#define DEBUG		/* Test */

#ifdef DEBUG
#define dbg_printf(args...)     printf(args)
#else
#define dbg_printf(args...)
#endif

#define CHAIN_LEN_TARGET		1
#define CHAIN_LEN_RESIZE_THRESHOLD	2

#ifndef max
#define max(a, b)	((a) > (b) ? (a) : (b))
#endif

#define REMOVED_FLAG		(1UL << 0)
#define FLAGS_MASK		((1UL << 1) - 1)

struct rcu_table {
	unsigned long size;	/* always a power of 2 */
	unsigned long resize_target;
	int resize_initiated;
	struct rcu_head head;
	struct rcu_ht_node *tbl[0];
};

struct rcu_ht {
	struct rcu_table *t;		/* shared */
	ht_hash_fct hash_fct;
	ht_compare_fct compare_fct;
	unsigned long hash_seed;
	pthread_mutex_t resize_mutex;	/* resize mutex: add/del mutex */
	unsigned int in_progress_resize;
	void (*ht_call_rcu)(struct rcu_head *head,
		      void (*func)(struct rcu_head *head));
};

struct rcu_resize_work {
	struct rcu_head head;
	struct rcu_ht *ht;
};

/*
 * Algorithm to reverse bits in a word by lookup table, extended to
 * 64-bit words.
 * Source:
 * http://graphics.stanford.edu/~seander/bithacks.html#BitReverseTable
 * Originally from Public Domain.
 */

static const uint8_t BitReverseTable256[256] = 
{
#define R2(n) (n),   (n) + 2*64,     (n) + 1*64,     (n) + 3*64
#define R4(n) R2(n), R2((n) + 2*16), R2((n) + 1*16), R2((n) + 3*16)
#define R6(n) R4(n), R4((n) + 2*4 ), R4((n) + 1*4 ), R4((n) + 3*4 )
	R6(0), R6(2), R6(1), R6(3)
};
#undef R2
#undef R4
#undef R6

static
uint8_t bit_reverse_u8(uint8_t v)
{
	return BitReverseTable256[v];
}

static __attribute__((unused))
uint32_t bit_reverse_u32(uint32_t v)
{
	return ((uint32_t) bit_reverse_u8(v) << 24) | 
		((uint32_t) bit_reverse_u8(v >> 8) << 16) | 
		((uint32_t) bit_reverse_u8(v >> 16) << 8) | 
		((uint32_t) bit_reverse_u8(v >> 24));
}

static __attribute__((unused))
uint64_t bit_reverse_u64(uint64_t v)
{
	return ((uint64_t) bit_reverse_u8(v) << 56) | 
		((uint64_t) bit_reverse_u8(v >> 8)  << 48) | 
		((uint64_t) bit_reverse_u8(v >> 16) << 40) |
		((uint64_t) bit_reverse_u8(v >> 24) << 32) |
		((uint64_t) bit_reverse_u8(v >> 32) << 24) | 
		((uint64_t) bit_reverse_u8(v >> 40) << 16) | 
		((uint64_t) bit_reverse_u8(v >> 48) << 8) |
		((uint64_t) bit_reverse_u8(v >> 56));
}

static
unsigned long bit_reverse_ulong(unsigned long v)
{
#if (CAA_BITS_PER_LONG == 32)
	return bit_reverse_u32(v);
#else
	return bit_reverse_u64(v);
#endif
}

/*
 * Algorithm to find the log2 of a 32-bit unsigned integer.
 * source: http://graphics.stanford.edu/~seander/bithacks.html#IntegerLogLookup
 * Originally from Public Domain.
 */
static const char LogTable256[256] = 
{
#define LT(n) n, n, n, n, n, n, n, n, n, n, n, n, n, n, n, n
	-1, 0, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3,
	LT(4), LT(5), LT(5), LT(6), LT(6), LT(6), LT(6),
	LT(7), LT(7), LT(7), LT(7), LT(7), LT(7), LT(7), LT(7)
};

uint32_t log2_u32(uint32_t v)
{
	uint32_t t, tt;

	if ((tt = (v >> 16)))
		return (t = (tt >> 8))
				? 24 + LogTable256[t]
				: 16 + LogTable256[tt];
	else
		return (t = (v >> 8))
				? 8 + LogTable256[t]
				: LogTable256[v];
}

static
void ht_resize_lazy(struct rcu_ht *ht, struct rcu_table *t, int growth);

static
void check_resize(struct rcu_ht *ht, struct rcu_table *t,
		  uint32_t chain_len)
{
	if (chain_len >= CHAIN_LEN_RESIZE_THRESHOLD)
		ht_resize_lazy(ht, t,
			log2_u32(chain_len - CHAIN_LEN_TARGET - 1));
}

static
struct rcu_ht_node *clear_flag(struct rcu_ht_node *node)
{
	return (struct rcu_ht_node *) (((unsigned long) node) & ~FLAGS_MASK);
}

static
int is_removed(struct rcu_ht_node *node)
{
	return ((unsigned long) node) & REMOVED_FLAG;
}

static
struct rcu_ht_node *flag_removed(struct rcu_ht_node *node)
{
	return (struct rcu_ht_node *) (((unsigned long) node) | REMOVED_FLAG);
}

static
unsigned long _uatomic_max(unsigned long *ptr, unsigned long v)
{
	unsigned long old1, old2;

	old1 = uatomic_read(ptr);
	do {
		old2 = old1;
		if (old2 >= v)
			return old2;
	} while ((old1 = uatomic_cmpxchg(ptr, old2, v)) != old2);
	return v;
}

/*
 * Remove all logically deleted nodes from a bucket up to a certain node key.
 */
static
void _ht_gc_bucket(struct rcu_ht_node *dummy, struct rcu_ht_node *node)
{
	struct rcu_ht_node *iter_prev, *iter, *next;

	for (;;) {
		iter_prev = dummy;
		/* We can always skip the dummy node initially */
		iter = rcu_dereference(iter_prev->p.next);
		assert(iter_prev->p.reverse_hash <= node->p.reverse_hash);
		for (;;) {
			if (unlikely(!iter))
				return;
			if (clear_flag(iter)->p.reverse_hash > node->p.reverse_hash)
				return;
			next = rcu_dereference(clear_flag(iter)->p.next);
			if (is_removed(next))
				break;
			iter_prev = iter;
			iter = next;
		}
		assert(!is_removed(iter));
		(void) uatomic_cmpxchg(&iter_prev->p.next, iter, clear_flag(next));
	}
}

static
struct rcu_ht_node *_ht_add(struct rcu_ht *ht, struct rcu_table *t,
			    struct rcu_ht_node *node, int unique)
{
	struct rcu_ht_node *iter_prev, *dummy, *iter, *next;
	unsigned long hash;

	if (!t->size) {
		assert(node->p.dummy);
		return node;	/* Initial first add (head) */
	}
	hash = bit_reverse_ulong(node->p.reverse_hash);
	for (;;) {
		uint32_t chain_len = 0;

		/*
		 * iter_prev points to the non-removed node prior to the
		 * insert location.
		 */
		iter_prev = rcu_dereference(t->tbl[hash & (t->size - 1)]);
		/* We can always skip the dummy node initially */
		iter = rcu_dereference(iter_prev->p.next);
		assert(iter_prev->p.reverse_hash <= node->p.reverse_hash);
		for (;;) {
			if (unlikely(!iter))
				goto insert;
			if (clear_flag(iter)->p.reverse_hash > node->p.reverse_hash)
				goto insert;
			next = rcu_dereference(clear_flag(iter)->p.next);
			if (is_removed(next))
				goto gc_node;
			if (unique
			    && !clear_flag(iter)->p.dummy
			    && !ht->compare_fct(node->key, node->key_len,
						clear_flag(iter)->key,
						clear_flag(iter)->key_len))
				return clear_flag(iter);
			/* Only account for identical reverse hash once */
			if (iter_prev->p.reverse_hash != clear_flag(iter)->p.reverse_hash)
				check_resize(ht, t, ++chain_len);
			iter_prev = clear_flag(iter);
			iter = next;
		}
	insert:
		assert(node != clear_flag(iter));
		assert(!is_removed(iter_prev));
		assert(iter_prev != node);
		node->p.next = iter;
		if (uatomic_cmpxchg(&iter_prev->p.next, iter,
				    node) != iter)
			continue;	/* retry */
		else
			goto gc_end;
	gc_node:
		assert(!is_removed(iter));
		(void) uatomic_cmpxchg(&iter_prev->p.next, iter, clear_flag(next));
		/* retry */
	}
gc_end:
	/* Garbage collect logically removed nodes in the bucket */
	dummy = rcu_dereference(t->tbl[hash & (t->size - 1)]);
	_ht_gc_bucket(dummy, node);
	return node;
}

static
int _ht_remove(struct rcu_ht *ht, struct rcu_table *t, struct rcu_ht_node *node)
{
	struct rcu_ht_node *dummy, *next, *old;
	int flagged = 0;
	unsigned long hash;

	/* logically delete the node */
	old = rcu_dereference(node->p.next);
	do {
		next = old;
		if (is_removed(next))
			goto end;
		assert(!node->p.dummy);
		old = uatomic_cmpxchg(&node->p.next, next,
				      flag_removed(next));
	} while (old != next);

	/* We performed the (logical) deletion. */
	flagged = 1;

	/*
	 * Ensure that the node is not visible to readers anymore: lookup for
	 * the node, and remove it (along with any other logically removed node)
	 * if found.
	 */
	hash = bit_reverse_ulong(node->p.reverse_hash);
	dummy = rcu_dereference(t->tbl[hash & (t->size - 1)]);
	_ht_gc_bucket(dummy, node);
end:
	/*
	 * Only the flagging action indicated that we (and no other)
	 * removed the node from the hash.
	 */
	if (flagged) {
		assert(is_removed(rcu_dereference(node->p.next)));
		return 0;
	} else
		return -ENOENT;
}

static
void init_table(struct rcu_ht *ht, struct rcu_table *t,
		unsigned long first, unsigned long len)
{
	unsigned long i, end;

	end = first + len;
	for (i = first; i < end; i++) {
		/* Update table size when power of two */
		if (i != 0 && !(i & (i - 1)))
			t->size = i;
		t->tbl[i] = calloc(1, sizeof(struct _rcu_ht_node));
		t->tbl[i]->p.dummy = 1;
		t->tbl[i]->p.reverse_hash = bit_reverse_ulong(i);
		(void) _ht_add(ht, t, t->tbl[i], 0);
	}
	t->resize_target = t->size = end;
	t->resize_initiated = 0;
}

struct rcu_ht *ht_new(ht_hash_fct hash_fct,
		      ht_compare_fct compare_fct,
		      unsigned long hash_seed,
		      unsigned long init_size,
		      void (*ht_call_rcu)(struct rcu_head *head,
				void (*func)(struct rcu_head *head)))
{
	struct rcu_ht *ht;

	ht = calloc(1, sizeof(struct rcu_ht));
	ht->hash_fct = hash_fct;
	ht->compare_fct = compare_fct;
	ht->hash_seed = hash_seed;
	ht->ht_call_rcu = ht_call_rcu;
	ht->in_progress_resize = 0;
	/* this mutex should not nest in read-side C.S. */
	pthread_mutex_init(&ht->resize_mutex, NULL);
	ht->t = calloc(1, sizeof(struct rcu_table)
		       + (max(init_size, 1) * sizeof(struct rcu_ht_node *)));
	ht->t->size = 0;
	pthread_mutex_lock(&ht->resize_mutex);
	init_table(ht, ht->t, 0, max(init_size, 1));
	pthread_mutex_unlock(&ht->resize_mutex);
	return ht;
}

struct rcu_ht_node *ht_lookup(struct rcu_ht *ht, void *key, size_t key_len)
{
	struct rcu_table *t;
	struct rcu_ht_node *node;
	unsigned long hash, reverse_hash;

	hash = ht->hash_fct(key, key_len, ht->hash_seed);
	reverse_hash = bit_reverse_ulong(hash);

	t = rcu_dereference(ht->t);
	node = rcu_dereference(t->tbl[hash & (t->size - 1)]);
	for (;;) {
		if (unlikely(!node))
			break;
		if (unlikely(node->p.reverse_hash > reverse_hash)) {
			node = NULL;
			break;
		}
		if (likely(!is_removed(rcu_dereference(node->p.next)))
		    && !node->p.dummy
		    && likely(!ht->compare_fct(node->key, node->key_len, key, key_len))) {
				break;
		}
		node = clear_flag(rcu_dereference(node->p.next));
	}
	assert(!node || !node->p.dummy);
	return node;
}

void ht_add(struct rcu_ht *ht, struct rcu_ht_node *node)
{
	struct rcu_table *t;
	unsigned long hash;

	hash = ht->hash_fct(node->key, node->key_len, ht->hash_seed);
	node->p.reverse_hash = bit_reverse_ulong((unsigned long) hash);

	t = rcu_dereference(ht->t);
	(void) _ht_add(ht, t, node, 0);
}

struct rcu_ht_node *ht_add_unique(struct rcu_ht *ht, struct rcu_ht_node *node)
{
	struct rcu_table *t;
	unsigned long hash;

	hash = ht->hash_fct(node->key, node->key_len, ht->hash_seed);
	node->p.reverse_hash = bit_reverse_ulong((unsigned long) hash);

	t = rcu_dereference(ht->t);
	return _ht_add(ht, t, node, 1);
}

int ht_remove(struct rcu_ht *ht, struct rcu_ht_node *node)
{
	struct rcu_table *t;

	t = rcu_dereference(ht->t);
	return _ht_remove(ht, t, node);
}

static
int ht_delete_dummy(struct rcu_ht *ht)
{
	struct rcu_table *t;
	struct rcu_ht_node *node;
	unsigned long i;

	t = ht->t;
	/* Check that the table is empty */
	node = t->tbl[0];
	do {
		if (!node->p.dummy)
			return -EPERM;
		node = node->p.next;
		assert(!is_removed(node));
	} while (node);
	/* Internal sanity check: all nodes left should be dummy */
	for (i = 0; i < t->size; i++) {
		assert(t->tbl[i]->p.dummy);
		free(t->tbl[i]);
	}
	return 0;
}

/*
 * Should only be called when no more concurrent readers nor writers can
 * possibly access the table.
 */
int ht_destroy(struct rcu_ht *ht)
{
	int ret;

	/* Wait for in-flight resize operations to complete */
	while (uatomic_read(&ht->in_progress_resize))
		poll(NULL, 0, 100);	/* wait for 100ms */
	ret = ht_delete_dummy(ht);
	if (ret)
		return ret;
	free(ht->t);
	free(ht);
	return ret;
}

void ht_count_nodes(struct rcu_ht *ht,
		unsigned long *count,
		unsigned long *removed)
{
	struct rcu_table *t;
	struct rcu_ht_node *node, *next;

	*count = 0;
	*removed = 0;

	t = rcu_dereference(ht->t);
	/* Check that the table is empty */
	node = rcu_dereference(t->tbl[0]);
	do {
		next = rcu_dereference(node->p.next);
		if (is_removed(next)) {
			assert(!node->p.dummy);
			(*removed)++;
		} else if (!node->p.dummy)
			(*count)++;
		node = clear_flag(next);
	} while (node);
}

static
void ht_free_table_cb(struct rcu_head *head)
{
	struct rcu_table *t =
		caa_container_of(head, struct rcu_table, head);
	free(t);
}

/* called with resize mutex held */
static
void _do_ht_resize(struct rcu_ht *ht)
{
	unsigned long new_size, old_size;
	struct rcu_table *new_t, *old_t;

	old_t = ht->t;
	old_size = old_t->size;

	new_size = CMM_LOAD_SHARED(old_t->resize_target);
	dbg_printf("rculfhash: resize from %lu to %lu buckets\n",
		   old_size, new_size);
	if (old_size == new_size)
		return;
	new_t = malloc(sizeof(struct rcu_table)
			+ (new_size * sizeof(struct rcu_ht_node *)));
	assert(new_size > old_size);
	memcpy(&new_t->tbl, &old_t->tbl,
	       old_size * sizeof(struct rcu_ht_node *));
	init_table(ht, new_t, old_size, new_size - old_size);
	/* Changing table and size atomically wrt lookups */
	rcu_assign_pointer(ht->t, new_t);
	ht->ht_call_rcu(&old_t->head, ht_free_table_cb);
}

static
unsigned long resize_target_update(struct rcu_table *t,
				   int growth_order)
{
	return _uatomic_max(&t->resize_target,
			    t->size << growth_order);
}

void ht_resize(struct rcu_ht *ht, int growth)
{
	struct rcu_table *t = rcu_dereference(ht->t);
	unsigned long target_size;

	target_size = resize_target_update(t, growth);
	if (t->size < target_size) {
		CMM_STORE_SHARED(t->resize_initiated, 1);
		pthread_mutex_lock(&ht->resize_mutex);
		_do_ht_resize(ht);
		pthread_mutex_unlock(&ht->resize_mutex);
	}
}

static
void do_resize_cb(struct rcu_head *head)
{
	struct rcu_resize_work *work =
		caa_container_of(head, struct rcu_resize_work, head);
	struct rcu_ht *ht = work->ht;

	pthread_mutex_lock(&ht->resize_mutex);
	_do_ht_resize(ht);
	pthread_mutex_unlock(&ht->resize_mutex);
	free(work);
	cmm_smp_mb();	/* finish resize before decrement */
	uatomic_dec(&ht->in_progress_resize);
}

static
void ht_resize_lazy(struct rcu_ht *ht, struct rcu_table *t, int growth)
{
	struct rcu_resize_work *work;
	unsigned long target_size;

	target_size = resize_target_update(t, growth);
	if (!CMM_LOAD_SHARED(t->resize_initiated) && t->size < target_size) {
		uatomic_inc(&ht->in_progress_resize);
		cmm_smp_mb();	/* increment resize count before calling it */
		work = malloc(sizeof(*work));
		work->ht = ht;
		ht->ht_call_rcu(&work->head, do_resize_cb);
		CMM_STORE_SHARED(t->resize_initiated, 1);
	}
}
