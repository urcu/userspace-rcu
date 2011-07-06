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

#define CHAIN_LEN_TARGET		4
#define CHAIN_LEN_RESIZE_THRESHOLD	16

#ifndef max
#define max(a, b)	((a) > (b) ? (a) : (b))
#endif

struct rcu_table {
	unsigned long size;	/* always a power of 2 */
	unsigned long resize_target;
	struct rcu_head head;
	struct rcu_ht_node *tbl[0];
};

struct rcu_ht {
	struct rcu_table *t;		/* shared */
	ht_hash_fct hash_fct;
	ht_compare_fct compare_fct;
	unsigned long hash_seed;
	pthread_mutex_t resize_mutex;	/* resize mutex: add/del mutex */
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
			log2_u32(chain_len - CHAIN_LEN_TARGET));
}

static
struct rcu_ht_node *clear_flag(struct rcu_ht_node *node)
{
	return (struct rcu_ht_node *) (((unsigned long) node) & ~0x1);
}

static
int is_removed(struct rcu_ht_node *node)
{
	return ((unsigned long) node) & 0x1;
}

static
struct rcu_ht_node *flag_removed(struct rcu_ht_node *node)
{
	return (struct rcu_ht_node *) (((unsigned long) node) | 0x1);
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

static
void _ht_add(struct rcu_ht *ht, struct rcu_table *t, struct rcu_ht_node *node)
{
	struct rcu_ht_node *iter_prev = NULL, *iter = NULL;

	if (!t->size)
		return;
	for (;;) {
		uint32_t chain_len = 0;

		iter_prev = rcu_dereference(t->tbl[node->hash & (t->size - 1)]);
		assert(iter_prev);
		assert(iter_prev->reverse_hash <= node->reverse_hash);
		for (;;) {
			iter = clear_flag(rcu_dereference(iter_prev->next));
			if (unlikely(!iter))
				break;
			if (iter->reverse_hash > node->reverse_hash)
				break;
			iter_prev = iter;
			check_resize(ht, t, ++chain_len);
		}
		/*
		 * add in iter_prev->next: TODO: check for helping
		 * delete, for lock-freedom...
		 */
		if (is_removed(iter))
			continue;
		assert(node != iter);
		node->next = iter;
		assert(iter_prev != node);
		if (uatomic_cmpxchg(&iter_prev->next, iter, node) != iter)
			continue;
		break;
	}
}

static
int _ht_remove(struct rcu_ht *ht, struct rcu_table *t, struct rcu_ht_node *node)
{
	struct rcu_ht_node *iter_prev, *iter, *next, *old;
	unsigned long chain_len;
	int found, ret = 0;
	int flagged = 0;

retry:
	chain_len = 0;
	found = 0;
	iter_prev = rcu_dereference(t->tbl[node->hash & (t->size - 1)]);
	assert(iter_prev);
	assert(iter_prev->reverse_hash <= node->reverse_hash);
	for (;;) {
		iter = clear_flag(rcu_dereference(iter_prev->next));
		if (unlikely(!iter))
			break;
		if (unlikely(iter->reverse_hash > node->reverse_hash))
			break;
		if (iter == node) {
			found = 1;
			break;
		}
		iter_prev = iter;
	} 
	if (!found) {
		ret = -ENOENT;
		goto end;
	}
	next = rcu_dereference(iter->next);
	if (!flagged) {
		if (is_removed(next)) {
			ret = -ENOENT;
			goto end;
		}
		/* set deletion flag */
		if ((old = uatomic_cmpxchg(&iter->next, next,
					   flag_removed(next))) != next) {
			if (old == flag_removed(next)) {
				ret = -ENOENT;
				goto end;
			} else {
				goto retry;
			}
		}
		flagged = 1;
	}
	/*
	 * Remove the element from the list.
	 * Retry if there has been a concurrent add before us.
	 * Retry if the prev node has been deleted.
	 * There cannot be a concurrent delete for our position, because
	 * we won the deletion flag cmpxchg.
	 * If there is a concurrent add after us, our deletion flag
	 * makes it busy-loop (FIXME: not lock-free).
	 */
	if (uatomic_cmpxchg(&iter_prev->next, iter, clear_flag(next)) != iter)
		goto retry;
end:
	return ret;
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
		t->tbl[i] = calloc(1, sizeof(struct rcu_ht_node));
		t->tbl[i]->dummy = 1;
		t->tbl[i]->hash = i;
		t->tbl[i]->reverse_hash = bit_reverse_ulong(i);
		_ht_add(ht, t, t->tbl[i]);
	}
	t->resize_target = t->size = end;
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
		if (unlikely(node->reverse_hash > reverse_hash)) {
			node = NULL;
			break;
		}
		if (!ht->compare_fct(node->key, node->key_len, key, key_len)) {
			if (unlikely(is_removed(rcu_dereference(node->next))))
				node = NULL;
			break;
		}
		node = clear_flag(rcu_dereference(node->next));
	}
	return node;
}

void ht_add(struct rcu_ht *ht, struct rcu_ht_node *node)
{
	struct rcu_table *t;

	node->hash = ht->hash_fct(node->key, node->key_len, ht->hash_seed);
	node->reverse_hash = bit_reverse_ulong((unsigned long) node->hash);

	t = rcu_dereference(ht->t);
	_ht_add(ht, t, node);
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
		if (!node->dummy)
			return -EPERM;
		node = node->next;
	} while (node);
	/* Internal sanity check: all nodes left should be dummy */
	for (i = 0; i < t->size; i++) {
		assert(t->tbl[i]->dummy);
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

	ret = ht_delete_dummy(ht);
	if (ret)
		return ret;
	free(ht->t);
	free(ht);
	return ret;
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
}

static
void ht_resize_lazy(struct rcu_ht *ht, struct rcu_table *t, int growth)
{
	struct rcu_resize_work *work;
	unsigned long target_size;

	target_size = resize_target_update(t, growth);
	if (t->size < target_size) {
		work = malloc(sizeof(*work));
		work->ht = ht;
		ht->ht_call_rcu(&work->head, do_resize_cb);
	}
}
