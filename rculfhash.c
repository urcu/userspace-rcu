/*
 * rculfhash.c
 *
 * Userspace RCU library - Lock-Free Resizable RCU Hash Table
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
 * Some specificities of this Lock-Free Resizable RCU Hash Table
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
 * - The resize operation for small tables only allows expanding the hash table.
 *   It is triggered automatically by detecting long chains in the add
 *   operation.
 * - The resize operation for larger tables (and available through an
 *   API) allows both expanding and shrinking the hash table.
 * - Per-CPU Split-counters are used to keep track of the number of
 *   nodes within the hash table for automatic resize triggering.
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
 * 
 * A bit of ascii art explanation:
 * 
 * Order index is the off-by-one compare to the actual power of 2 because 
 * we use index 0 to deal with the 0 special-case.
 * 
 * This shows the nodes for a small table ordered by reversed bits:
 * 
 *    bits   reverse
 * 0  000        000
 * 4  100        001
 * 2  010        010
 * 6  110        011
 * 1  001        100
 * 5  101        101
 * 3  011        110
 * 7  111        111
 * 
 * This shows the nodes in order of non-reversed bits, linked by 
 * reversed-bit order.
 * 
 * order              bits       reverse
 * 0               0  000        000
 *                 |
 * 1               |  1  001        100       <-    <-
 *                 |  |                        |     |
 * 2               |  |  2  010        010     |     |
 *                 |  |  |  3  011        110  | <-  |
 *                 |  |  |  |                  |  |  |
 * 3               -> |  |  |  4  100        001  |  |
 *                    -> |  |     5  101        101  |
 *                       -> |        6  110        011
 *                          ->          7  111        111
 */

#define _LGPL_SOURCE
#include <stdlib.h>
#include <errno.h>
#include <assert.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>

#include "config.h"
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

/*
 * Per-CPU split-counters lazily update the global counter each 1024
 * addition/removal. It automatically keeps track of resize required.
 * We use the bucket length as indicator for need to expand for small
 * tables and machines lacking per-cpu data suppport.
 */
#define COUNT_COMMIT_ORDER		10
#define CHAIN_LEN_TARGET		1
#define CHAIN_LEN_RESIZE_THRESHOLD	3

/*
 * Define the minimum table size.
 */
#define MIN_TABLE_SIZE			1

#if (CAA_BITS_PER_LONG == 32)
#define MAX_TABLE_ORDER			32
#else
#define MAX_TABLE_ORDER			64
#endif

#ifndef min
#define min(a, b)	((a) < (b) ? (a) : (b))
#endif

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

/* Value of the end pointer. Should not interact with flags. */
#define END_VALUE		NULL

struct ht_items_count {
	unsigned long add, remove;
} __attribute__((aligned(CAA_CACHE_LINE_SIZE)));

struct rcu_level {
	struct rcu_head head;
	struct _cds_lfht_node nodes[0];
};

struct rcu_table {
	unsigned long size;	/* always a power of 2, shared (RCU) */
	unsigned long resize_target;
	int resize_initiated;
	struct rcu_level *tbl[MAX_TABLE_ORDER];
};

struct cds_lfht {
	struct rcu_table t;
	cds_lfht_hash_fct hash_fct;
	cds_lfht_compare_fct compare_fct;
	unsigned long hash_seed;
	int flags;
	/*
	 * We need to put the work threads offline (QSBR) when taking this
	 * mutex, because we use synchronize_rcu within this mutex critical
	 * section, which waits on read-side critical sections, and could
	 * therefore cause grace-period deadlock if we hold off RCU G.P.
	 * completion.
	 */
	pthread_mutex_t resize_mutex;	/* resize mutex: add/del mutex */
	unsigned int in_progress_resize, in_progress_destroy;
	void (*cds_lfht_call_rcu)(struct rcu_head *head,
		      void (*func)(struct rcu_head *head));
	void (*cds_lfht_synchronize_rcu)(void);
	void (*cds_lfht_rcu_read_lock)(void);
	void (*cds_lfht_rcu_read_unlock)(void);
	void (*cds_lfht_rcu_thread_offline)(void);
	void (*cds_lfht_rcu_thread_online)(void);
	unsigned long count;		/* global approximate item count */
	struct ht_items_count *percpu_count;	/* per-cpu item count */
};

struct rcu_resize_work {
	struct rcu_head head;
	struct cds_lfht *ht;
};

static
struct cds_lfht_node *_cds_lfht_add(struct cds_lfht *ht,
				unsigned long size,
				struct cds_lfht_node *node,
				int unique, int dummy);

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

#ifdef POISON_FREE
#define poison_free(ptr)				\
	do {						\
		memset(ptr, 0x42, sizeof(*(ptr)));	\
		free(ptr);				\
	} while (0)
#else
#define poison_free(ptr)	free(ptr)
#endif

static
void cds_lfht_resize_lazy(struct cds_lfht *ht, unsigned long size, int growth);

/*
 * If the sched_getcpu() and sysconf(_SC_NPROCESSORS_CONF) calls are
 * available, then we support hash table item accounting.
 * In the unfortunate event the number of CPUs reported would be
 * inaccurate, we use modulo arithmetic on the number of CPUs we got.
 */
#if defined(HAVE_SCHED_GETCPU) && defined(HAVE_SYSCONF)

static
void cds_lfht_resize_lazy_count(struct cds_lfht *ht, unsigned long size,
				unsigned long count);

static long nr_cpus_mask = -1;

static
struct ht_items_count *alloc_per_cpu_items_count(void)
{
	struct ht_items_count *count;

	switch (nr_cpus_mask) {
	case -2:
		return NULL;
	case -1:
	{
		long maxcpus;

		maxcpus = sysconf(_SC_NPROCESSORS_CONF);
		if (maxcpus <= 0) {
			nr_cpus_mask = -2;
			return NULL;
		}
		/*
		 * round up number of CPUs to next power of two, so we
		 * can use & for modulo.
		 */
		maxcpus = 1UL << get_count_order_ulong(maxcpus);
		nr_cpus_mask = maxcpus - 1;
	}
		/* Fall-through */
	default:
		return calloc(nr_cpus_mask + 1, sizeof(*count));
	}
}

static
void free_per_cpu_items_count(struct ht_items_count *count)
{
	poison_free(count);
}

static
int ht_get_cpu(void)
{
	int cpu;

	assert(nr_cpus_mask >= 0);
	cpu = sched_getcpu();
	if (unlikely(cpu < 0))
		return cpu;
	else
		return cpu & nr_cpus_mask;
}

static
void ht_count_add(struct cds_lfht *ht, unsigned long size)
{
	unsigned long percpu_count;
	int cpu;

	if (unlikely(!ht->percpu_count))
		return;
	cpu = ht_get_cpu();
	if (unlikely(cpu < 0))
		return;
	percpu_count = uatomic_add_return(&ht->percpu_count[cpu].add, 1);
	if (unlikely(!(percpu_count & ((1UL << COUNT_COMMIT_ORDER) - 1)))) {
		unsigned long count;

		dbg_printf("add percpu %lu\n", percpu_count);
		count = uatomic_add_return(&ht->count,
					   1UL << COUNT_COMMIT_ORDER);
		/* If power of 2 */
		if (!(count & (count - 1))) {
			if ((count >> CHAIN_LEN_RESIZE_THRESHOLD) < size)
				return;
			dbg_printf("add set global %lu\n", count);
			cds_lfht_resize_lazy_count(ht, size,
				count >> (CHAIN_LEN_TARGET - 1));
		}
	}
}

static
void ht_count_remove(struct cds_lfht *ht, unsigned long size)
{
	unsigned long percpu_count;
	int cpu;

	if (unlikely(!ht->percpu_count))
		return;
	cpu = ht_get_cpu();
	if (unlikely(cpu < 0))
		return;
	percpu_count = uatomic_add_return(&ht->percpu_count[cpu].remove, -1);
	if (unlikely(!(percpu_count & ((1UL << COUNT_COMMIT_ORDER) - 1)))) {
		unsigned long count;

		dbg_printf("remove percpu %lu\n", percpu_count);
		count = uatomic_add_return(&ht->count,
					   -(1UL << COUNT_COMMIT_ORDER));
		/* If power of 2 */
		if (!(count & (count - 1))) {
			if ((count >> CHAIN_LEN_RESIZE_THRESHOLD) >= size)
				return;
			dbg_printf("remove set global %lu\n", count);
			cds_lfht_resize_lazy_count(ht, size,
				count >> (CHAIN_LEN_TARGET - 1));
		}
	}
}

#else /* #if defined(HAVE_SCHED_GETCPU) && defined(HAVE_SYSCONF) */

static const long nr_cpus_mask = -1;

static
struct ht_items_count *alloc_per_cpu_items_count(void)
{
	return NULL;
}

static
void free_per_cpu_items_count(struct ht_items_count *count)
{
}

static
void ht_count_add(struct cds_lfht *ht, unsigned long size)
{
}

static
void ht_count_remove(struct cds_lfht *ht, unsigned long size)
{
}

#endif /* #else #if defined(HAVE_SCHED_GETCPU) && defined(HAVE_SYSCONF) */


static
void check_resize(struct cds_lfht *ht, unsigned long size, uint32_t chain_len)
{
	unsigned long count;

	if (!(ht->flags & CDS_LFHT_AUTO_RESIZE))
		return;
	count = uatomic_read(&ht->count);
	/*
	 * Use bucket-local length for small table expand and for
	 * environments lacking per-cpu data support.
	 */
	if (count >= (1UL << COUNT_COMMIT_ORDER))
		return;
	if (chain_len > 100)
		dbg_printf("WARNING: large chain length: %u.\n",
			   chain_len);
	if (chain_len >= CHAIN_LEN_RESIZE_THRESHOLD)
		cds_lfht_resize_lazy(ht, size,
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
struct cds_lfht_node *get_end(void)
{
	return (struct cds_lfht_node *) END_VALUE;
}

static
int is_end(struct cds_lfht_node *node)
{
	return clear_flag(node) == (struct cds_lfht_node *) END_VALUE;
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
void cds_lfht_free_level(struct rcu_head *head)
{
	struct rcu_level *l =
		caa_container_of(head, struct rcu_level, head);
	poison_free(l);
}

/*
 * Remove all logically deleted nodes from a bucket up to a certain node key.
 */
static
void _cds_lfht_gc_bucket(struct cds_lfht_node *dummy, struct cds_lfht_node *node)
{
	struct cds_lfht_node *iter_prev, *iter, *next, *new_next;

	assert(!is_dummy(dummy));
	assert(!is_removed(dummy));
	assert(!is_dummy(node));
	assert(!is_removed(node));
	for (;;) {
		iter_prev = dummy;
		/* We can always skip the dummy node initially */
		iter = rcu_dereference(iter_prev->p.next);
		assert(iter_prev->p.reverse_hash <= node->p.reverse_hash);
		/*
		 * We should never be called with dummy (start of chain)
		 * and logically removed node (end of path compression
		 * marker) being the actual same node. This would be a
		 * bug in the algorithm implementation.
		 */
		assert(dummy != node);
		for (;;) {
			if (unlikely(is_end(iter)))
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
	return;
}

static
struct cds_lfht_node *_cds_lfht_add(struct cds_lfht *ht,
				unsigned long size,
				struct cds_lfht_node *node,
				int unique, int dummy)
{
	struct cds_lfht_node *iter_prev, *iter, *next, *new_node, *new_next,
			*dummy_node;
	struct _cds_lfht_node *lookup;
	unsigned long hash, index, order;

	assert(!is_dummy(node));
	assert(!is_removed(node));
	if (!size) {
		assert(dummy);
		node->p.next = flag_dummy(get_end());
		return node;	/* Initial first add (head) */
	}
	hash = bit_reverse_ulong(node->p.reverse_hash);
	for (;;) {
		uint32_t chain_len = 0;

		/*
		 * iter_prev points to the non-removed node prior to the
		 * insert location.
		 */
		index = hash & (size - 1);
		order = get_count_order_ulong(index + 1);
		lookup = &ht->t.tbl[order]->nodes[index & ((!order ? 0 : (1UL << (order - 1))) - 1)];
		iter_prev = (struct cds_lfht_node *) lookup;
		/* We can always skip the dummy node initially */
		iter = rcu_dereference(iter_prev->p.next);
		assert(iter_prev->p.reverse_hash <= node->p.reverse_hash);
		for (;;) {
			if (unlikely(is_end(iter)))
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
				check_resize(ht, size, ++chain_len);
			iter_prev = clear_flag(iter);
			iter = next;
		}
	insert:
		assert(node != clear_flag(iter));
		assert(!is_removed(iter_prev));
		assert(!is_removed(iter));
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
		assert(new_next != NULL);
		(void) uatomic_cmpxchg(&iter_prev->p.next, iter, new_next);
		/* retry */
	}
gc_end:
	/* Garbage collect logically removed nodes in the bucket */
	index = hash & (size - 1);
	order = get_count_order_ulong(index + 1);
	lookup = &ht->t.tbl[order]->nodes[index & (!order ? 0 : ((1UL << (order - 1)) - 1))];
	dummy_node = (struct cds_lfht_node *) lookup;
	_cds_lfht_gc_bucket(dummy_node, node);
	return node;
}

static
int _cds_lfht_remove(struct cds_lfht *ht, unsigned long size,
		struct cds_lfht_node *node,
		int dummy_removal)
{
	struct cds_lfht_node *dummy, *next, *old;
	struct _cds_lfht_node *lookup;
	int flagged = 0;
	unsigned long hash, index, order;

	/* logically delete the node */
	assert(!is_dummy(node));
	assert(!is_removed(node));
	old = rcu_dereference(node->p.next);
	do {
		next = old;
		if (unlikely(is_removed(next)))
			goto end;
		if (dummy_removal)
			assert(is_dummy(next));
		else
			assert(!is_dummy(next));
		assert(next != NULL);
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
	assert(size > 0);
	index = hash & (size - 1);
	order = get_count_order_ulong(index + 1);
	lookup = &ht->t.tbl[order]->nodes[index & (!order ? 0 : ((1UL << (order - 1)) - 1))];
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
void init_table_hash(struct cds_lfht *ht, unsigned long i,
		unsigned long len)
{
	unsigned long j;

	for (j = 0; j < len; j++) {
		struct cds_lfht_node *new_node =
			(struct cds_lfht_node *) &ht->t.tbl[i]->nodes[j];

		dbg_printf("init hash entry: i %lu j %lu hash %lu\n",
			   i, j, !i ? 0 : (1UL << (i - 1)) + j);
		new_node->p.reverse_hash =
			bit_reverse_ulong(!i ? 0 : (1UL << (i - 1)) + j);
		if (CMM_LOAD_SHARED(ht->in_progress_destroy))
			break;
	}
}

/*
 * Holding RCU read lock to protect _cds_lfht_add against memory
 * reclaim that could be performed by other call_rcu worker threads (ABA
 * problem).
 */
static
void init_table_link(struct cds_lfht *ht, unsigned long i, unsigned long len)
{
	unsigned long j;

	ht->cds_lfht_rcu_thread_online();
	ht->cds_lfht_rcu_read_lock();
	for (j = 0; j < len; j++) {
		struct cds_lfht_node *new_node =
			(struct cds_lfht_node *) &ht->t.tbl[i]->nodes[j];

		dbg_printf("init link: i %lu j %lu hash %lu\n",
			   i, j, !i ? 0 : (1UL << (i - 1)) + j);
		(void) _cds_lfht_add(ht, !i ? 0 : (1UL << (i - 1)),
				new_node, 0, 1);
		if (CMM_LOAD_SHARED(ht->in_progress_destroy))
			break;
	}
	ht->cds_lfht_rcu_read_unlock();
	ht->cds_lfht_rcu_thread_offline();
}

static
void init_table(struct cds_lfht *ht,
		unsigned long first_order, unsigned long len_order)
{
	unsigned long i, end_order;

	dbg_printf("init table: first_order %lu end_order %lu\n",
		   first_order, first_order + len_order);
	end_order = first_order + len_order;
	for (i = first_order; i < end_order; i++) {
		unsigned long len;

		len = !i ? 1 : 1UL << (i - 1);
		dbg_printf("init order %lu len: %lu\n", i, len);

		/* Stop expand if the resize target changes under us */
		if (CMM_LOAD_SHARED(ht->t.resize_target) < (!i ? 1 : (1UL << i)))
			break;

		ht->t.tbl[i] = calloc(1, sizeof(struct rcu_level)
				+ (len * sizeof(struct _cds_lfht_node)));

		/* Set all dummy nodes reverse hash values for a level */
		init_table_hash(ht, i, len);

		/*
		 * Link all dummy nodes into the table. Concurrent
		 * add/remove are helping us.
		 */
		init_table_link(ht, i, len);

		/*
		 * Update table size.
		 */
		cmm_smp_wmb();	/* populate data before RCU size */
		CMM_STORE_SHARED(ht->t.size, !i ? 1 : (1UL << i));

		dbg_printf("init new size: %lu\n", !i ? 1 : (1UL << i));
		if (CMM_LOAD_SHARED(ht->in_progress_destroy))
			break;
	}
}

/*
 * Holding RCU read lock to protect _cds_lfht_remove against memory
 * reclaim that could be performed by other call_rcu worker threads (ABA
 * problem).
 * For a single level, we logically remove and garbage collect each node.
 *
 * As a design choice, we perform logical removal and garbage collection on a
 * node-per-node basis to simplify this algorithm. We also assume keeping good
 * cache locality of the operation would overweight possible performance gain
 * that could be achieved by batching garbage collection for multiple levels.
 * However, this would have to be justified by benchmarks.
 *
 * Concurrent removal and add operations are helping us perform garbage
 * collection of logically removed nodes. We guarantee that all logically
 * removed nodes have been garbage-collected (unlinked) before call_rcu is
 * invoked to free a hole level of dummy nodes (after a grace period).
 *
 * Logical removal and garbage collection can therefore be done in batch or on a
 * node-per-node basis, as long as the guarantee above holds.
 */
static
void remove_table(struct cds_lfht *ht, unsigned long i, unsigned long len)
{
	unsigned long j;

	ht->cds_lfht_rcu_thread_online();
	ht->cds_lfht_rcu_read_lock();
	for (j = 0; j < len; j++) {
		struct cds_lfht_node *fini_node =
			(struct cds_lfht_node *) &ht->t.tbl[i]->nodes[j];

		dbg_printf("remove entry: i %lu j %lu hash %lu\n",
			   i, j, !i ? 0 : (1UL << (i - 1)) + j);
		fini_node->p.reverse_hash =
			bit_reverse_ulong(!i ? 0 : (1UL << (i - 1)) + j);
		(void) _cds_lfht_remove(ht, !i ? 0 : (1UL << (i - 1)),
				fini_node, 1);
		if (CMM_LOAD_SHARED(ht->in_progress_destroy))
			break;
	}
	ht->cds_lfht_rcu_read_unlock();
	ht->cds_lfht_rcu_thread_offline();
}

static
void fini_table(struct cds_lfht *ht,
		unsigned long first_order, unsigned long len_order)
{
	long i, end_order;

	dbg_printf("fini table: first_order %lu end_order %lu\n",
		   first_order, first_order + len_order);
	end_order = first_order + len_order;
	assert(first_order > 0);
	for (i = end_order - 1; i >= first_order; i--) {
		unsigned long len;

		len = !i ? 1 : 1UL << (i - 1);
		dbg_printf("fini order %lu len: %lu\n", i, len);

		/* Stop shrink if the resize target changes under us */
		if (CMM_LOAD_SHARED(ht->t.resize_target) > (1UL << (i - 1)))
			break;

		cmm_smp_wmb();	/* populate data before RCU size */
		CMM_STORE_SHARED(ht->t.size, 1UL << (i - 1));

		/*
		 * We need to wait for all add operations to reach Q.S. (and
		 * thus use the new table for lookups) before we can start
		 * releasing the old dummy nodes. Otherwise their lookup will
		 * return a logically removed node as insert position.
		 */
		ht->cds_lfht_synchronize_rcu();

		/*
		 * Set "removed" flag in dummy nodes about to be removed.
		 * Unlink all now-logically-removed dummy node pointers.
		 * Concurrent add/remove operation are helping us doing
		 * the gc.
		 */
		remove_table(ht, i, len);

		ht->cds_lfht_call_rcu(&ht->t.tbl[i]->head, cds_lfht_free_level);

		dbg_printf("fini new size: %lu\n", 1UL << i);
		if (CMM_LOAD_SHARED(ht->in_progress_destroy))
			break;
	}
}

struct cds_lfht *cds_lfht_new(cds_lfht_hash_fct hash_fct,
			cds_lfht_compare_fct compare_fct,
			unsigned long hash_seed,
			unsigned long init_size,
			int flags,
			void (*cds_lfht_call_rcu)(struct rcu_head *head,
					void (*func)(struct rcu_head *head)),
			void (*cds_lfht_synchronize_rcu)(void),
			void (*cds_lfht_rcu_read_lock)(void),
			void (*cds_lfht_rcu_read_unlock)(void),
			void (*cds_lfht_rcu_thread_offline)(void),
			void (*cds_lfht_rcu_thread_online)(void))
{
	struct cds_lfht *ht;
	unsigned long order;

	/* init_size must be power of two */
	if (init_size && (init_size & (init_size - 1)))
		return NULL;
	ht = calloc(1, sizeof(struct cds_lfht));
	ht->hash_fct = hash_fct;
	ht->compare_fct = compare_fct;
	ht->hash_seed = hash_seed;
	ht->cds_lfht_call_rcu = cds_lfht_call_rcu;
	ht->cds_lfht_synchronize_rcu = cds_lfht_synchronize_rcu;
	ht->cds_lfht_rcu_read_lock = cds_lfht_rcu_read_lock;
	ht->cds_lfht_rcu_read_unlock = cds_lfht_rcu_read_unlock;
	ht->cds_lfht_rcu_thread_offline = cds_lfht_rcu_thread_offline;
	ht->cds_lfht_rcu_thread_online = cds_lfht_rcu_thread_online;
	ht->percpu_count = alloc_per_cpu_items_count();
	/* this mutex should not nest in read-side C.S. */
	pthread_mutex_init(&ht->resize_mutex, NULL);
	order = get_count_order_ulong(max(init_size, MIN_TABLE_SIZE)) + 1;
	ht->flags = flags;
	ht->cds_lfht_rcu_thread_offline();
	pthread_mutex_lock(&ht->resize_mutex);
	ht->t.resize_target = 1UL << (order - 1);
	init_table(ht, 0, order);
	pthread_mutex_unlock(&ht->resize_mutex);
	ht->cds_lfht_rcu_thread_online();
	return ht;
}

struct cds_lfht_node *cds_lfht_lookup(struct cds_lfht *ht, void *key, size_t key_len)
{
	struct cds_lfht_node *node, *next, *dummy_node;
	struct _cds_lfht_node *lookup;
	unsigned long hash, reverse_hash, index, order, size;

	hash = ht->hash_fct(key, key_len, ht->hash_seed);
	reverse_hash = bit_reverse_ulong(hash);

	size = rcu_dereference(ht->t.size);
	index = hash & (size - 1);
	order = get_count_order_ulong(index + 1);
	lookup = &ht->t.tbl[order]->nodes[index & (!order ? 0 : ((1UL << (order - 1))) - 1)];
	dbg_printf("lookup hash %lu index %lu order %lu aridx %lu\n",
		   hash, index, order, index & (!order ? 0 : ((1UL << (order - 1)) - 1)));
	dummy_node = (struct cds_lfht_node *) lookup;
	/* We can always skip the dummy node initially */
	node = rcu_dereference(dummy_node->p.next);
	node = clear_flag(node);
	for (;;) {
		if (unlikely(is_end(node))) {
			node = NULL;
			break;
		}
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

struct cds_lfht_node *cds_lfht_next(struct cds_lfht *ht,
				struct cds_lfht_node *node)
{
	struct cds_lfht_node *next;
	unsigned long reverse_hash;
	void *key;
	size_t key_len;

	reverse_hash = node->p.reverse_hash;
	key = node->key;
	key_len = node->key_len;
	next = rcu_dereference(node->p.next);
	node = clear_flag(next);

	for (;;) {
		if (unlikely(is_end(node))) {
			node = NULL;
			break;
		}
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
	unsigned long hash, size;

	hash = ht->hash_fct(node->key, node->key_len, ht->hash_seed);
	node->p.reverse_hash = bit_reverse_ulong((unsigned long) hash);

	size = rcu_dereference(ht->t.size);
	(void) _cds_lfht_add(ht, size, node, 0, 0);
	ht_count_add(ht, size);
}

struct cds_lfht_node *cds_lfht_add_unique(struct cds_lfht *ht,
					struct cds_lfht_node *node)
{
	unsigned long hash, size;
	struct cds_lfht_node *ret;

	hash = ht->hash_fct(node->key, node->key_len, ht->hash_seed);
	node->p.reverse_hash = bit_reverse_ulong((unsigned long) hash);

	size = rcu_dereference(ht->t.size);
	ret = _cds_lfht_add(ht, size, node, 1, 0);
	if (ret == node)
		ht_count_add(ht, size);
	return ret;
}

int cds_lfht_remove(struct cds_lfht *ht, struct cds_lfht_node *node)
{
	unsigned long size;
	int ret;

	size = rcu_dereference(ht->t.size);
	ret = _cds_lfht_remove(ht, size, node, 0);
	if (!ret)
		ht_count_remove(ht, size);
	return ret;
}

static
int cds_lfht_delete_dummy(struct cds_lfht *ht)
{
	struct cds_lfht_node *node;
	struct _cds_lfht_node *lookup;
	unsigned long order, i, size;

	/* Check that the table is empty */
	lookup = &ht->t.tbl[0]->nodes[0];
	node = (struct cds_lfht_node *) lookup;
	do {
		node = clear_flag(node)->p.next;
		if (!is_dummy(node))
			return -EPERM;
		assert(!is_removed(node));
	} while (!is_end(node));
	/*
	 * size accessed without rcu_dereference because hash table is
	 * being destroyed.
	 */
	size = ht->t.size;
	/* Internal sanity check: all nodes left should be dummy */
	for (order = 0; order < get_count_order_ulong(size) + 1; order++) {
		unsigned long len;

		len = !order ? 1 : 1UL << (order - 1);
		for (i = 0; i < len; i++) {
			dbg_printf("delete order %lu i %lu hash %lu\n",
				order, i,
				bit_reverse_ulong(ht->t.tbl[order]->nodes[i].reverse_hash));
			assert(is_dummy(ht->t.tbl[order]->nodes[i].next));
		}
		poison_free(ht->t.tbl[order]);
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
	free_per_cpu_items_count(ht->percpu_count);
	poison_free(ht);
	return ret;
}

void cds_lfht_count_nodes(struct cds_lfht *ht,
		unsigned long *count,
		unsigned long *removed)
{
	struct cds_lfht_node *node, *next;
	struct _cds_lfht_node *lookup;
	unsigned long nr_dummy = 0;

	*count = 0;
	*removed = 0;

	/* Count non-dummy nodes in the table */
	lookup = &ht->t.tbl[0]->nodes[0];
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
	} while (!is_end(node));
	dbg_printf("number of dummy nodes: %lu\n", nr_dummy);
}

/* called with resize mutex held */
static
void _do_cds_lfht_grow(struct cds_lfht *ht,
		unsigned long old_size, unsigned long new_size)
{
	unsigned long old_order, new_order;

	old_order = get_count_order_ulong(old_size) + 1;
	new_order = get_count_order_ulong(new_size) + 1;
	printf("resize from %lu (order %lu) to %lu (order %lu) buckets\n",
	       old_size, old_order, new_size, new_order);
	assert(new_size > old_size);
	init_table(ht, old_order, new_order - old_order);
}

/* called with resize mutex held */
static
void _do_cds_lfht_shrink(struct cds_lfht *ht,
		unsigned long old_size, unsigned long new_size)
{
	unsigned long old_order, new_order;

	new_size = max(new_size, MIN_TABLE_SIZE);
	old_order = get_count_order_ulong(old_size) + 1;
	new_order = get_count_order_ulong(new_size) + 1;
	printf("resize from %lu (order %lu) to %lu (order %lu) buckets\n",
	       old_size, old_order, new_size, new_order);
	assert(new_size < old_size);

	/* Remove and unlink all dummy nodes to remove. */
	fini_table(ht, new_order, old_order - new_order);
}


/* called with resize mutex held */
static
void _do_cds_lfht_resize(struct cds_lfht *ht)
{
	unsigned long new_size, old_size;

	/*
	 * Resize table, re-do if the target size has changed under us.
	 */
	do {
		ht->t.resize_initiated = 1;
		old_size = ht->t.size;
		new_size = CMM_LOAD_SHARED(ht->t.resize_target);
		if (old_size < new_size)
			_do_cds_lfht_grow(ht, old_size, new_size);
		else if (old_size > new_size)
			_do_cds_lfht_shrink(ht, old_size, new_size);
		ht->t.resize_initiated = 0;
		/* write resize_initiated before read resize_target */
		cmm_smp_mb();
	} while (ht->t.size != CMM_LOAD_SHARED(ht->t.resize_target));
}

static
unsigned long resize_target_update(struct cds_lfht *ht, unsigned long size,
				   int growth_order)
{
	return _uatomic_max(&ht->t.resize_target,
			    size << growth_order);
}

static
void resize_target_update_count(struct cds_lfht *ht,
				unsigned long count)
{
	count = max(count, MIN_TABLE_SIZE);
	uatomic_set(&ht->t.resize_target, count);
}

void cds_lfht_resize(struct cds_lfht *ht, unsigned long new_size)
{
	resize_target_update_count(ht, new_size);
	CMM_STORE_SHARED(ht->t.resize_initiated, 1);
	ht->cds_lfht_rcu_thread_offline();
	pthread_mutex_lock(&ht->resize_mutex);
	_do_cds_lfht_resize(ht);
	pthread_mutex_unlock(&ht->resize_mutex);
	ht->cds_lfht_rcu_thread_online();
}

static
void do_resize_cb(struct rcu_head *head)
{
	struct rcu_resize_work *work =
		caa_container_of(head, struct rcu_resize_work, head);
	struct cds_lfht *ht = work->ht;

	ht->cds_lfht_rcu_thread_offline();
	pthread_mutex_lock(&ht->resize_mutex);
	_do_cds_lfht_resize(ht);
	pthread_mutex_unlock(&ht->resize_mutex);
	ht->cds_lfht_rcu_thread_online();
	poison_free(work);
	cmm_smp_mb();	/* finish resize before decrement */
	uatomic_dec(&ht->in_progress_resize);
}

static
void cds_lfht_resize_lazy(struct cds_lfht *ht, unsigned long size, int growth)
{
	struct rcu_resize_work *work;
	unsigned long target_size;

	target_size = resize_target_update(ht, size, growth);
	/* Store resize_target before read resize_initiated */
	cmm_smp_mb();
	if (!CMM_LOAD_SHARED(ht->t.resize_initiated) && size < target_size) {
		uatomic_inc(&ht->in_progress_resize);
		cmm_smp_mb();	/* increment resize count before calling it */
		work = malloc(sizeof(*work));
		work->ht = ht;
		ht->cds_lfht_call_rcu(&work->head, do_resize_cb);
		CMM_STORE_SHARED(ht->t.resize_initiated, 1);
	}
}

#if defined(HAVE_SCHED_GETCPU) && defined(HAVE_SYSCONF)

static
void cds_lfht_resize_lazy_count(struct cds_lfht *ht, unsigned long size,
				unsigned long count)
{
	struct rcu_resize_work *work;

	if (!(ht->flags & CDS_LFHT_AUTO_RESIZE))
		return;
	resize_target_update_count(ht, count);
	/* Store resize_target before read resize_initiated */
	cmm_smp_mb();
	if (!CMM_LOAD_SHARED(ht->t.resize_initiated)) {
		uatomic_inc(&ht->in_progress_resize);
		cmm_smp_mb();	/* increment resize count before calling it */
		work = malloc(sizeof(*work));
		work->ht = ht;
		ht->cds_lfht_call_rcu(&work->head, do_resize_cb);
		CMM_STORE_SHARED(ht->t.resize_initiated, 1);
	}
}

#endif
