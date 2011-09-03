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

/*
 * Based on the following articles:
 * - Ori Shalev and Nir Shavit. Split-ordered lists: Lock-free
 *   extensible hash tables. J. ACM 53, 3 (May 2006), 379-405.
 * - Michael, M. M. High performance dynamic lock-free hash tables
 *   and list-based sets. In Proceedings of the fourteenth annual ACM
 *   symposium on Parallel algorithms and architectures, ACM Press,
 *   (2002), 73-82.
 *
 * Some specificities of this Lock-Free Expandable RCU Hash Table
 * implementation:
 *
 * - RCU read-side critical section allows readers to perform hash
 *   table lookups and use the returned objects safely by delaying
 *   memory reclaim of a grace period.
 * - Add and remove operations are lock-free, and do not need to
 *   allocate memory. They need to be executed within RCU read-side
 *   critical section to ensure the objects they read are valid and to
 *   deal with the cmpxchg ABA problem.
 * - add and add_unique operations are supported. add_unique checks if
 *   the node key already exists in the hash table. It ensures no key
 *   duplicata exists.
 * - The resize operation executes concurrently with add/remove/lookup.
 * - Hash table nodes are contained within a split-ordered list. This
 *   list is ordered by incrementing reversed-bits-hash value.
 * - An index of dummy nodes is kept. These dummy nodes are the hash
 *   table "buckets", and they are also chained together in the
 *   split-ordered list, which allows recursive expansion.
 * - The resize operation only allows expanding the hash table.
 *   It is triggered either through an API call or automatically by
 *   detecting long chains in the add operation.
 * - Resize operation initiated by long chain detection is executed by a
 *   call_rcu thread, which keeps lock-freedom of add and remove.
 * - Resize operations are protected by a mutex.
 * - The removal operation is split in two parts: first, a "removed"
 *   flag is set in the next pointer within the node to remove. Then,
 *   a "garbage collection" is performed in the bucket containing the
 *   removed node (from the start of the bucket up to the removed node).
 *   All encountered nodes with "removed" flag set in their next
 *   pointers are removed from the linked-list. If the cmpxchg used for
 *   removal fails (due to concurrent garbage-collection or concurrent
 *   add), we retry from the beginning of the bucket. This ensures that
 *   the node with "removed" flag set is removed from the hash table
 *   (not visible to lookups anymore) before the RCU read-side critical
 *   section held across removal ends. Furthermore, this ensures that
 *   the node with "removed" flag set is removed from the linked-list
 *   before its memory is reclaimed. Only the thread which removal
 *   successfully set the "removed" flag (with a cmpxchg) into a node's
 *   next pointer is considered to have succeeded its removal (and thus
 *   owns the node to reclaim). Because we garbage-collect starting from
 *   an invariant node (the start-of-bucket dummy node) up to the
 *   "removed" node (or find a reverse-hash that is higher), we are sure
 *   that a successful traversal of the chain leads to a chain that is
 *   present in the linked-list (the start node is never removed) and
 *   that is does not contain the "removed" node anymore, even if
 *   concurrent delete/add operations are changing the structure of the
 *   list concurrently.
 * - The add operation performs gargage collection of buckets if it
 *   encounters nodes with removed flag set in the bucket where it wants
 *   to add its new node. This ensures lock-freedom of add operation by
 *   helping the remover unlink nodes from the list rather than to wait
 *   for it do to so.
 * - A RCU "order table" indexed by log2(hash index) is copied and
 *   expanded by the resize operation. This order table allows finding
 *   the "dummy node" tables.
 * - There is one dummy node table per hash index order. The size of
 *   each dummy node table is half the number of hashes contained in
 *   this order.
 * - call_rcu is used to garbage-collect the old order table.
 * - The per-order dummy node tables contain a compact version of the
 *   hash table nodes. These tables are invariant after they are
 *   populated into the hash table.
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

#ifdef DEBUG
#define dbg_printf(fmt, args...)     printf("[debug rculfhash] " fmt, ## args)
#else
#define dbg_printf(fmt, args...)
#endif

#define CHAIN_LEN_TARGET		4
#define CHAIN_LEN_RESIZE_THRESHOLD	8

#ifndef max
#define max(a, b)	((a) > (b) ? (a) : (b))
#endif

/*
 * The removed flag needs to be updated atomically with the pointer.
 * The dummy flag does not require to be updated atomically with the
 * pointer, but it is added as a pointer low bit flag to save space.
 */
#define REMOVED_FLAG		(1UL << 0)
#define DUMMY_FLAG		(1UL << 1)
#define FLAGS_MASK		((1UL << 2) - 1)

struct rcu_table {
	unsigned long size;	/* always a power of 2 */
	unsigned long resize_target;
	int resize_initiated;
	struct rcu_head head;
	struct _cds_lfht_node *tbl[0];
};

struct cds_lfht {
	struct rcu_table *t;		/* shared */
	cds_lfht_hash_fct hash_fct;
	cds_lfht_compare_fct compare_fct;
	unsigned long hash_seed;
	pthread_mutex_t resize_mutex;	/* resize mutex: add/del mutex */
	unsigned int in_progress_resize, in_progress_destroy;
	void (*cds_lfht_call_rcu)(struct rcu_head *head,
		      void (*func)(struct rcu_head *head));
};

struct rcu_resize_work {
	struct rcu_head head;
	struct cds_lfht *ht;
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
 * fls: returns the position of the most significant bit.
 * Returns 0 if no bit is set, else returns the position of the most
 * significant bit (from 1 to 32 on 32-bit, from 1 to 64 on 64-bit).
 */
#if defined(__i386) || defined(__x86_64)
static inline
unsigned int fls_u32(uint32_t x)
{
	int r;

	asm("bsrl %1,%0\n\t"
	    "jnz 1f\n\t"
	    "movl $-1,%0\n\t"
	    "1:\n\t"
	    : "=r" (r) : "rm" (x));
	return r + 1;
}
#define HAS_FLS_U32
#endif

#if defined(__x86_64)
static inline
unsigned int fls_u64(uint64_t x)
{
	long r;

	asm("bsrq %1,%0\n\t"
	    "jnz 1f\n\t"
	    "movq $-1,%0\n\t"
	    "1:\n\t"
	    : "=r" (r) : "rm" (x));
	return r + 1;
}
#define HAS_FLS_U64
#endif

#ifndef HAS_FLS_U64
static __attribute__((unused))
unsigned int fls_u64(uint64_t x)
{
	unsigned int r = 64;

	if (!x)
		return 0;

	if (!(x & 0xFFFFFFFF00000000ULL)) {
		x <<= 32;
		r -= 32;
	}
	if (!(x & 0xFFFF000000000000ULL)) {
		x <<= 16;
		r -= 16;
	}
	if (!(x & 0xFF00000000000000ULL)) {
		x <<= 8;
		r -= 8;
	}
	if (!(x & 0xF000000000000000ULL)) {
		x <<= 4;
		r -= 4;
	}
	if (!(x & 0xC000000000000000ULL)) {
		x <<= 2;
		r -= 2;
	}
	if (!(x & 0x8000000000000000ULL)) {
		x <<= 1;
		r -= 1;
	}
	return r;
}
#endif

#ifndef HAS_FLS_U32
static __attribute__((unused))
unsigned int fls_u32(uint32_t x)
{
	unsigned int r = 32;

	if (!x)
		return 0;
	if (!(x & 0xFFFF0000U)) {
		x <<= 16;
		r -= 16;
	}
	if (!(x & 0xFF000000U)) {
		x <<= 8;
		r -= 8;
	}
	if (!(x & 0xF0000000U)) {
		x <<= 4;
		r -= 4;
	}
	if (!(x & 0xC0000000U)) {
		x <<= 2;
		r -= 2;
	}
	if (!(x & 0x80000000U)) {
		x <<= 1;
		r -= 1;
	}
	return r;
}
#endif

unsigned int fls_ulong(unsigned long x)
{
#if (CAA_BITS_PER_lONG == 32)
	return fls_u32(x);
#else
	return fls_u64(x);
#endif
}

int get_count_order_u32(uint32_t x)
{
	int order;

	order = fls_u32(x) - 1;
	if (x & (x - 1))
		order++;
	return order;
}

int get_count_order_ulong(unsigned long x)
{
	int order;

	order = fls_ulong(x) - 1;
	if (x & (x - 1))
		order++;
	return order;
}

static
void cds_lfht_resize_lazy(struct cds_lfht *ht, struct rcu_table *t, int growth);

static
void check_resize(struct cds_lfht *ht, struct rcu_table *t,
		  uint32_t chain_len)
{
	if (chain_len > 100)
		dbg_printf("WARNING: large chain length: %u.\n",
			   chain_len);
	if (chain_len >= CHAIN_LEN_RESIZE_THRESHOLD)
		cds_lfht_resize_lazy(ht, t,
			get_count_order_u32(chain_len - (CHAIN_LEN_TARGET - 1)));
}

static
struct cds_lfht_node *clear_flag(struct cds_lfht_node *node)
{
	return (struct cds_lfht_node *) (((unsigned long) node) & ~FLAGS_MASK);
}

static
int is_removed(struct cds_lfht_node *node)
{
	return ((unsigned long) node) & REMOVED_FLAG;
}

static
struct cds_lfht_node *flag_removed(struct cds_lfht_node *node)
{
	return (struct cds_lfht_node *) (((unsigned long) node) | REMOVED_FLAG);
}

static
int is_dummy(struct cds_lfht_node *node)
{
	return ((unsigned long) node) & DUMMY_FLAG;
}

static
struct cds_lfht_node *flag_dummy(struct cds_lfht_node *node)
{
	return (struct cds_lfht_node *) (((unsigned long) node) | DUMMY_FLAG);
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
void _cds_lfht_gc_bucket(struct cds_lfht_node *dummy, struct cds_lfht_node *node)
{
	struct cds_lfht_node *iter_prev, *iter, *next, *new_next;

	for (;;) {
		iter_prev = dummy;
		/* We can always skip the dummy node initially */
		iter = rcu_dereference(iter_prev->p.next);
		assert(iter_prev->p.reverse_hash <= node->p.reverse_hash);
		for (;;) {
			if (unlikely(!clear_flag(iter)))
				return;
			if (likely(clear_flag(iter)->p.reverse_hash > node->p.reverse_hash))
				return;
			next = rcu_dereference(clear_flag(iter)->p.next);
			if (likely(is_removed(next)))
				break;
			iter_prev = clear_flag(iter);
			iter = next;
		}
		assert(!is_removed(iter));
		if (is_dummy(iter))
			new_next = flag_dummy(clear_flag(next));
		else
			new_next = clear_flag(next);
		(void) uatomic_cmpxchg(&iter_prev->p.next, iter, new_next);
	}
}

static
struct cds_lfht_node *_cds_lfht_add(struct cds_lfht *ht, struct rcu_table *t,
				struct cds_lfht_node *node, int unique, int dummy)
{
	struct cds_lfht_node *iter_prev, *iter, *next, *new_node, *new_next,
			*dummy_node;
	struct _cds_lfht_node *lookup;
	unsigned long hash, index, order;

	if (!t->size) {
		assert(dummy);
		node->p.next = flag_dummy(NULL);
		return node;	/* Initial first add (head) */
	}
	hash = bit_reverse_ulong(node->p.reverse_hash);
	for (;;) {
		uint32_t chain_len = 0;

		/*
		 * iter_prev points to the non-removed node prior to the
		 * insert location.
		 */
		index = hash & (t->size - 1);
		order = get_count_order_ulong(index + 1);
		lookup = &t->tbl[order][index & ((1UL << (order - 1)) - 1)];
		iter_prev = (struct cds_lfht_node *) lookup;
		/* We can always skip the dummy node initially */
		iter = rcu_dereference(iter_prev->p.next);
		assert(iter_prev->p.reverse_hash <= node->p.reverse_hash);
		for (;;) {
			if (unlikely(!clear_flag(iter)))
				goto insert;
			if (likely(clear_flag(iter)->p.reverse_hash > node->p.reverse_hash))
				goto insert;
			next = rcu_dereference(clear_flag(iter)->p.next);
			if (unlikely(is_removed(next)))
				goto gc_node;
			if (unique
			    && !is_dummy(next)
			    && !ht->compare_fct(node->key, node->key_len,
						clear_flag(iter)->key,
						clear_flag(iter)->key_len))
				return clear_flag(iter);
			/* Only account for identical reverse hash once */
			if (iter_prev->p.reverse_hash != clear_flag(iter)->p.reverse_hash
			    && !is_dummy(next))
				check_resize(ht, t, ++chain_len);
			iter_prev = clear_flag(iter);
			iter = next;
		}
	insert:
		assert(node != clear_flag(iter));
		assert(!is_removed(iter_prev));
		assert(iter_prev != node);
		if (!dummy)
			node->p.next = clear_flag(iter);
		else
			node->p.next = flag_dummy(clear_flag(iter));
		if (is_dummy(iter))
			new_node = flag_dummy(node);
		else
			new_node = node;
		if (uatomic_cmpxchg(&iter_prev->p.next, iter,
				    new_node) != iter)
			continue;	/* retry */
		else
			goto gc_end;
	gc_node:
		assert(!is_removed(iter));
		if (is_dummy(iter))
			new_next = flag_dummy(clear_flag(next));
		else
			new_next = clear_flag(next);
		(void) uatomic_cmpxchg(&iter_prev->p.next, iter, new_next);
		/* retry */
	}
gc_end:
	/* Garbage collect logically removed nodes in the bucket */
	index = hash & (t->size - 1);
	order = get_count_order_ulong(index + 1);
	lookup = &t->tbl[order][index & ((1UL << (order - 1)) - 1)];
	dummy_node = (struct cds_lfht_node *) lookup;
	_cds_lfht_gc_bucket(dummy_node, node);
	return node;
}

static
int _cds_lfht_remove(struct cds_lfht *ht, struct rcu_table *t,
		struct cds_lfht_node *node)
{
	struct cds_lfht_node *dummy, *next, *old;
	struct _cds_lfht_node *lookup;
	int flagged = 0;
	unsigned long hash, index, order;

	/* logically delete the node */
	old = rcu_dereference(node->p.next);
	do {
		next = old;
		if (unlikely(is_removed(next)))
			goto end;
		assert(!is_dummy(next));
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
	index = hash & (t->size - 1);
	order = get_count_order_ulong(index + 1);
	lookup = &t->tbl[order][index & ((1UL << (order - 1)) - 1)];
	dummy = (struct cds_lfht_node *) lookup;
	_cds_lfht_gc_bucket(dummy, node);
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
void init_table(struct cds_lfht *ht, struct rcu_table *t,
		unsigned long first_order, unsigned long len_order)
{
	unsigned long i, end_order;

	dbg_printf("init table: first_order %lu end_order %lu\n",
		   first_order, first_order + len_order);
	end_order = first_order + len_order;
	t->size = !first_order ? 0 : (1UL << (first_order - 1));
	for (i = first_order; i < end_order; i++) {
		unsigned long j, len;

		len = !i ? 1 : 1UL << (i - 1);
		dbg_printf("init order %lu len: %lu\n", i, len);
		t->tbl[i] = calloc(len, sizeof(struct _cds_lfht_node));
		for (j = 0; j < len; j++) {
			dbg_printf("init entry: i %lu j %lu hash %lu\n",
				   i, j, !i ? 0 : (1UL << (i - 1)) + j);
			struct cds_lfht_node *new_node =
				(struct cds_lfht_node *) &t->tbl[i][j];
			new_node->p.reverse_hash =
				bit_reverse_ulong(!i ? 0 : (1UL << (i - 1)) + j);
			(void) _cds_lfht_add(ht, t, new_node, 0, 1);
			if (CMM_LOAD_SHARED(ht->in_progress_destroy))
				break;
		}
		/* Update table size */
		t->size = !i ? 1 : (1UL << i);
		dbg_printf("init new size: %lu\n", t->size);
		if (CMM_LOAD_SHARED(ht->in_progress_destroy))
			break;
	}
	t->resize_target = t->size;
	t->resize_initiated = 0;
}

struct cds_lfht *cds_lfht_new(cds_lfht_hash_fct hash_fct,
			cds_lfht_compare_fct compare_fct,
			unsigned long hash_seed,
			unsigned long init_size,
			void (*cds_lfht_call_rcu)(struct rcu_head *head,
					void (*func)(struct rcu_head *head)))
{
	struct cds_lfht *ht;
	unsigned long order;

	/* init_size must be power of two */
	if (init_size & (init_size - 1))
		return NULL;
	ht = calloc(1, sizeof(struct cds_lfht));
	ht->hash_fct = hash_fct;
	ht->compare_fct = compare_fct;
	ht->hash_seed = hash_seed;
	ht->cds_lfht_call_rcu = cds_lfht_call_rcu;
	ht->in_progress_resize = 0;
	/* this mutex should not nest in read-side C.S. */
	pthread_mutex_init(&ht->resize_mutex, NULL);
	order = get_count_order_ulong(max(init_size, 1)) + 1;
	ht->t = calloc(1, sizeof(struct cds_lfht)
		       + (order * sizeof(struct _cds_lfht_node *)));
	ht->t->size = 0;
	pthread_mutex_lock(&ht->resize_mutex);
	init_table(ht, ht->t, 0, order);
	pthread_mutex_unlock(&ht->resize_mutex);
	return ht;
}

struct cds_lfht_node *cds_lfht_lookup(struct cds_lfht *ht, void *key, size_t key_len)
{
	struct rcu_table *t;
	struct cds_lfht_node *node, *next;
	struct _cds_lfht_node *lookup;
	unsigned long hash, reverse_hash, index, order;

	hash = ht->hash_fct(key, key_len, ht->hash_seed);
	reverse_hash = bit_reverse_ulong(hash);

	t = rcu_dereference(ht->t);
	index = hash & (t->size - 1);
	order = get_count_order_ulong(index + 1);
	lookup = &t->tbl[order][index & ((1UL << (order - 1)) - 1)];
	dbg_printf("lookup hash %lu index %lu order %lu aridx %lu\n",
		   hash, index, order, index & ((1UL << (order - 1)) - 1));
	node = (struct cds_lfht_node *) lookup;
	for (;;) {
		if (unlikely(!node))
			break;
		if (unlikely(node->p.reverse_hash > reverse_hash)) {
			node = NULL;
			break;
		}
		next = rcu_dereference(node->p.next);
		if (likely(!is_removed(next))
		    && !is_dummy(next)
		    && likely(!ht->compare_fct(node->key, node->key_len, key, key_len))) {
				break;
		}
		node = clear_flag(next);
	}
	assert(!node || !is_dummy(rcu_dereference(node->p.next)));
	return node;
}

void cds_lfht_add(struct cds_lfht *ht, struct cds_lfht_node *node)
{
	struct rcu_table *t;
	unsigned long hash;

	hash = ht->hash_fct(node->key, node->key_len, ht->hash_seed);
	node->p.reverse_hash = bit_reverse_ulong((unsigned long) hash);

	t = rcu_dereference(ht->t);
	(void) _cds_lfht_add(ht, t, node, 0, 0);
}

struct cds_lfht_node *cds_lfht_add_unique(struct cds_lfht *ht,
					struct cds_lfht_node *node)
{
	struct rcu_table *t;
	unsigned long hash;

	hash = ht->hash_fct(node->key, node->key_len, ht->hash_seed);
	node->p.reverse_hash = bit_reverse_ulong((unsigned long) hash);

	t = rcu_dereference(ht->t);
	return _cds_lfht_add(ht, t, node, 1, 0);
}

int cds_lfht_remove(struct cds_lfht *ht, struct cds_lfht_node *node)
{
	struct rcu_table *t;

	t = rcu_dereference(ht->t);
	return _cds_lfht_remove(ht, t, node);
}

static
int cds_lfht_delete_dummy(struct cds_lfht *ht)
{
	struct rcu_table *t;
	struct cds_lfht_node *node;
	struct _cds_lfht_node *lookup;
	unsigned long order, i;

	t = ht->t;
	/* Check that the table is empty */
	lookup = &t->tbl[0][0];
	node = (struct cds_lfht_node *) lookup;
	do {
		node = clear_flag(node)->p.next;
		if (!is_dummy(node))
			return -EPERM;
		assert(!is_removed(node));
	} while (clear_flag(node));
	/* Internal sanity check: all nodes left should be dummy */
	for (order = 0; order < get_count_order_ulong(t->size) + 1; order++) {
		unsigned long len;

		len = !order ? 1 : 1UL << (order - 1);
		for (i = 0; i < len; i++) {
			dbg_printf("delete order %lu i %lu hash %lu\n",
				order, i,
				bit_reverse_ulong(t->tbl[order][i].reverse_hash));
			assert(is_dummy(t->tbl[order][i].next));
		}
		free(t->tbl[order]);
	}
	return 0;
}

/*
 * Should only be called when no more concurrent readers nor writers can
 * possibly access the table.
 */
int cds_lfht_destroy(struct cds_lfht *ht)
{
	int ret;

	/* Wait for in-flight resize operations to complete */
	CMM_STORE_SHARED(ht->in_progress_destroy, 1);
	while (uatomic_read(&ht->in_progress_resize))
		poll(NULL, 0, 100);	/* wait for 100ms */
	ret = cds_lfht_delete_dummy(ht);
	if (ret)
		return ret;
	free(ht->t);
	free(ht);
	return ret;
}

void cds_lfht_count_nodes(struct cds_lfht *ht,
		unsigned long *count,
		unsigned long *removed)
{
	struct rcu_table *t;
	struct cds_lfht_node *node, *next;
	struct _cds_lfht_node *lookup;
	unsigned long nr_dummy = 0;

	*count = 0;
	*removed = 0;

	t = rcu_dereference(ht->t);
	/* Count non-dummy nodes in the table */
	lookup = &t->tbl[0][0];
	node = (struct cds_lfht_node *) lookup;
	do {
		next = rcu_dereference(node->p.next);
		if (is_removed(next)) {
			assert(!is_dummy(next));
			(*removed)++;
		} else if (!is_dummy(next))
			(*count)++;
		else
			(nr_dummy)++;
		node = clear_flag(next);
	} while (node);
	dbg_printf("number of dummy nodes: %lu\n", nr_dummy);
}

static
void cds_lfht_free_table_cb(struct rcu_head *head)
{
	struct rcu_table *t =
		caa_container_of(head, struct rcu_table, head);
	free(t);
}

/* called with resize mutex held */
static
void _do_cds_lfht_resize(struct cds_lfht *ht)
{
	unsigned long new_size, old_size, old_order, new_order;
	struct rcu_table *new_t, *old_t;

	old_t = ht->t;
	old_size = old_t->size;
	old_order = get_count_order_ulong(old_size) + 1;

	new_size = CMM_LOAD_SHARED(old_t->resize_target);
	if (old_size == new_size)
		return;
	new_order = get_count_order_ulong(new_size) + 1;
	dbg_printf("resize from %lu (order %lu) to %lu (order %lu) buckets\n",
	       old_size, old_order, new_size, new_order);
	new_t = malloc(sizeof(struct cds_lfht)
			+ (new_order * sizeof(struct _cds_lfht_node *)));
	assert(new_size > old_size);
	memcpy(&new_t->tbl, &old_t->tbl,
	       old_order * sizeof(struct _cds_lfht_node *));
	init_table(ht, new_t, old_order, new_order - old_order);
	/* Changing table and size atomically wrt lookups */
	rcu_assign_pointer(ht->t, new_t);
	ht->cds_lfht_call_rcu(&old_t->head, cds_lfht_free_table_cb);
}

static
unsigned long resize_target_update(struct rcu_table *t,
				   int growth_order)
{
	return _uatomic_max(&t->resize_target,
			    t->size << growth_order);
}

void cds_lfht_resize(struct cds_lfht *ht, int growth)
{
	struct rcu_table *t = rcu_dereference(ht->t);
	unsigned long target_size;

	if (growth < 0) {
		/*
		 * Silently refuse to shrink hash table. (not supported)
		 */
		dbg_printf("shrinking hash table not supported.\n");
		return;
	}

	target_size = resize_target_update(t, growth);
	if (t->size < target_size) {
		CMM_STORE_SHARED(t->resize_initiated, 1);
		pthread_mutex_lock(&ht->resize_mutex);
		_do_cds_lfht_resize(ht);
		pthread_mutex_unlock(&ht->resize_mutex);
	}
}

static
void do_resize_cb(struct rcu_head *head)
{
	struct rcu_resize_work *work =
		caa_container_of(head, struct rcu_resize_work, head);
	struct cds_lfht *ht = work->ht;

	pthread_mutex_lock(&ht->resize_mutex);
	_do_cds_lfht_resize(ht);
	pthread_mutex_unlock(&ht->resize_mutex);
	free(work);
	cmm_smp_mb();	/* finish resize before decrement */
	uatomic_dec(&ht->in_progress_resize);
}

static
void cds_lfht_resize_lazy(struct cds_lfht *ht, struct rcu_table *t, int growth)
{
	struct rcu_resize_work *work;
	unsigned long target_size;

	target_size = resize_target_update(t, growth);
	if (!CMM_LOAD_SHARED(t->resize_initiated) && t->size < target_size) {
		uatomic_inc(&ht->in_progress_resize);
		cmm_smp_mb();	/* increment resize count before calling it */
		work = malloc(sizeof(*work));
		work->ht = ht;
		ht->cds_lfht_call_rcu(&work->head, do_resize_cb);
		CMM_STORE_SHARED(t->resize_initiated, 1);
	}
}
