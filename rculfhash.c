/*
 * rculfhash.c
 *
 * Userspace RCU library - Lock-Free Resizable RCU Hash Table
 *
 * Copyright 2010-2011 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 * Copyright 2011 - Lai Jiangshan <laijs@cn.fujitsu.com>
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
 * - An index of bucket nodes is kept. These bucket nodes are the hash
 *   table "buckets", and they are also chained together in the
 *   split-ordered list, which allows recursive expansion.
 * - The resize operation for small tables only allows expanding the hash table.
 *   It is triggered automatically by detecting long chains in the add
 *   operation.
 * - The resize operation for larger tables (and available through an
 *   API) allows both expanding and shrinking the hash table.
 * - Split-counters are used to keep track of the number of
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
 *   an invariant node (the start-of-bucket bucket node) up to the
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
 *   the "bucket node" tables.
 * - There is one bucket node table per hash index order. The size of
 *   each bucket node table is half the number of hashes contained in
 *   this order (except for order 0).
 * - synchronzie_rcu is used to garbage-collect the old bucket node table.
 * - The per-order bucket node tables contain a compact version of the
 *   hash table nodes. These tables are invariant after they are
 *   populated into the hash table.
 *
 * Bucket node tables:
 *
 * hash table	hash table	the last	all bucket node tables
 * order	size		bucket node	0   1   2   3   4   5   6(index)
 * 				table size
 * 0		1		1		1
 * 1		2		1		1   1
 * 2		4		2		1   1   2
 * 3		8		4		1   1   2   4
 * 4		16		8		1   1   2   4   8
 * 5		32		16		1   1   2   4   8  16
 * 6		64		32		1   1   2   4   8  16  32
 *
 * When growing/shrinking, we only focus on the last bucket node table
 * which size is (!order ? 1 : (1 << (order -1))).
 *
 * Example for growing/shrinking:
 * grow hash table from order 5 to 6: init the index=6 bucket node table
 * shrink hash table from order 6 to 5: fini the index=6 bucket node table
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
 * 1               |  1  001        100             <-
 * 2               |  |  2  010        010    <-     |
 *                 |  |  |  3  011        110  | <-  |
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
 * Split-counters lazily update the global counter each 1024
 * addition/removal. It automatically keeps track of resize required.
 * We use the bucket length as indicator for need to expand for small
 * tables and machines lacking per-cpu data suppport.
 */
#define COUNT_COMMIT_ORDER		10
#define DEFAULT_SPLIT_COUNT_MASK	0xFUL
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

/*
 * Minimum number of bucket nodes to touch per thread to parallelize grow/shrink.
 */
#define MIN_PARTITION_PER_THREAD_ORDER	12
#define MIN_PARTITION_PER_THREAD	(1UL << MIN_PARTITION_PER_THREAD_ORDER)

#ifndef min
#define min(a, b)	((a) < (b) ? (a) : (b))
#endif

#ifndef max
#define max(a, b)	((a) > (b) ? (a) : (b))
#endif

/*
 * The removed flag needs to be updated atomically with the pointer.
 * It indicates that no node must attach to the node scheduled for
 * removal, and that node garbage collection must be performed.
 * The bucket flag does not require to be updated atomically with the
 * pointer, but it is added as a pointer low bit flag to save space.
 */
#define REMOVED_FLAG		(1UL << 0)
#define BUCKET_FLAG		(1UL << 1)
#define FLAGS_MASK		((1UL << 2) - 1)

/* Value of the end pointer. Should not interact with flags. */
#define END_VALUE		NULL

/*
 * ht_items_count: Split-counters counting the number of node addition
 * and removal in the table. Only used if the CDS_LFHT_ACCOUNTING flag
 * is set at hash table creation.
 *
 * These are free-running counters, never reset to zero. They count the
 * number of add/remove, and trigger every (1 << COUNT_COMMIT_ORDER)
 * operations to update the global counter. We choose a power-of-2 value
 * for the trigger to deal with 32 or 64-bit overflow of the counter.
 */
struct ht_items_count {
	unsigned long add, del;
} __attribute__((aligned(CAA_CACHE_LINE_SIZE)));

/*
 * rcu_level: Contains the per order-index-level bucket node table. The
 * size of each bucket node table is half the number of hashes contained
 * in this order (except for order 0). The minimum allocation size
 * parameter allows combining the bucket node arrays of the lowermost
 * levels to improve cache locality for small index orders.
 */
struct rcu_level {
	/* Note: manually update allocation length when adding a field */
	struct cds_lfht_node nodes[0];
};

/*
 * rcu_table: Contains the size and desired new size if a resize
 * operation is in progress, as well as the statically-sized array of
 * rcu_level pointers.
 */
struct rcu_table {
	unsigned long size;	/* always a power of 2, shared (RCU) */
	unsigned long resize_target;
	int resize_initiated;
	struct rcu_level *tbl[MAX_TABLE_ORDER];
};

/*
 * cds_lfht: Top-level data structure representing a lock-free hash
 * table. Defined in the implementation file to make it be an opaque
 * cookie to users.
 */
struct cds_lfht {
	struct rcu_table t;
	unsigned long min_alloc_order;
	unsigned long min_alloc_size;
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
	void (*cds_lfht_rcu_register_thread)(void);
	void (*cds_lfht_rcu_unregister_thread)(void);
	pthread_attr_t *resize_attr;	/* Resize threads attributes */
	long count;			/* global approximate item count */
	struct ht_items_count *split_count;	/* split item count */
};

/*
 * rcu_resize_work: Contains arguments passed to RCU worker thread
 * responsible for performing lazy resize.
 */
struct rcu_resize_work {
	struct rcu_head head;
	struct cds_lfht *ht;
};

/*
 * partition_resize_work: Contains arguments passed to worker threads
 * executing the hash table resize on partitions of the hash table
 * assigned to each processor's worker thread.
 */
struct partition_resize_work {
	pthread_t thread_id;
	struct cds_lfht *ht;
	unsigned long i, start, len;
	void (*fct)(struct cds_lfht *ht, unsigned long i,
		    unsigned long start, unsigned long len);
};

static
void _cds_lfht_add(struct cds_lfht *ht,
		cds_lfht_match_fct match,
		const void *key,
		unsigned long size,
		struct cds_lfht_node *node,
		struct cds_lfht_iter *unique_ret,
		int bucket);

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
#if (CAA_BITS_PER_LONG == 32)
	return fls_u32(x);
#else
	return fls_u64(x);
#endif
}

/*
 * Return the minimum order for which x <= (1UL << order).
 * Return -1 if x is 0.
 */
int get_count_order_u32(uint32_t x)
{
	if (!x)
		return -1;

	return fls_u32(x - 1);
}

/*
 * Return the minimum order for which x <= (1UL << order).
 * Return -1 if x is 0.
 */
int get_count_order_ulong(unsigned long x)
{
	if (!x)
		return -1;

	return fls_ulong(x - 1);
}

#ifdef POISON_FREE
#define poison_free(ptr)					\
	do {							\
		if (ptr) {					\
			memset(ptr, 0x42, sizeof(*(ptr)));	\
			free(ptr);				\
		}						\
	} while (0)
#else
#define poison_free(ptr)	free(ptr)
#endif

static
void cds_lfht_resize_lazy_grow(struct cds_lfht *ht, unsigned long size, int growth);

static
void cds_lfht_resize_lazy_count(struct cds_lfht *ht, unsigned long size,
				unsigned long count);

static long nr_cpus_mask = -1;
static long split_count_mask = -1;

#if defined(HAVE_SYSCONF)
static void ht_init_nr_cpus_mask(void)
{
	long maxcpus;

	maxcpus = sysconf(_SC_NPROCESSORS_CONF);
	if (maxcpus <= 0) {
		nr_cpus_mask = -2;
		return;
	}
	/*
	 * round up number of CPUs to next power of two, so we
	 * can use & for modulo.
	 */
	maxcpus = 1UL << get_count_order_ulong(maxcpus);
	nr_cpus_mask = maxcpus - 1;
}
#else /* #if defined(HAVE_SYSCONF) */
static void ht_init_nr_cpus_mask(void)
{
	nr_cpus_mask = -2;
}
#endif /* #else #if defined(HAVE_SYSCONF) */

static
void alloc_split_items_count(struct cds_lfht *ht)
{
	struct ht_items_count *count;

	if (nr_cpus_mask == -1)	{
		ht_init_nr_cpus_mask();
		if (nr_cpus_mask < 0)
			split_count_mask = DEFAULT_SPLIT_COUNT_MASK;
		else
			split_count_mask = nr_cpus_mask;
	}

	assert(split_count_mask >= 0);

	if (ht->flags & CDS_LFHT_ACCOUNTING) {
		ht->split_count = calloc(split_count_mask + 1, sizeof(*count));
		assert(ht->split_count);
	} else {
		ht->split_count = NULL;
	}
}

static
void free_split_items_count(struct cds_lfht *ht)
{
	poison_free(ht->split_count);
}

#if defined(HAVE_SCHED_GETCPU)
static
int ht_get_split_count_index(unsigned long hash)
{
	int cpu;

	assert(split_count_mask >= 0);
	cpu = sched_getcpu();
	if (caa_unlikely(cpu < 0))
		return hash & split_count_mask;
	else
		return cpu & split_count_mask;
}
#else /* #if defined(HAVE_SCHED_GETCPU) */
static
int ht_get_split_count_index(unsigned long hash)
{
	return hash & split_count_mask;
}
#endif /* #else #if defined(HAVE_SCHED_GETCPU) */

static
void ht_count_add(struct cds_lfht *ht, unsigned long size, unsigned long hash)
{
	unsigned long split_count;
	int index;

	if (caa_unlikely(!ht->split_count))
		return;
	index = ht_get_split_count_index(hash);
	split_count = uatomic_add_return(&ht->split_count[index].add, 1);
	if (caa_unlikely(!(split_count & ((1UL << COUNT_COMMIT_ORDER) - 1)))) {
		long count;

		dbg_printf("add split count %lu\n", split_count);
		count = uatomic_add_return(&ht->count,
					   1UL << COUNT_COMMIT_ORDER);
		/* If power of 2 */
		if (!(count & (count - 1))) {
			if ((count >> CHAIN_LEN_RESIZE_THRESHOLD) < size)
				return;
			dbg_printf("add set global %ld\n", count);
			cds_lfht_resize_lazy_count(ht, size,
				count >> (CHAIN_LEN_TARGET - 1));
		}
	}
}

static
void ht_count_del(struct cds_lfht *ht, unsigned long size, unsigned long hash)
{
	unsigned long split_count;
	int index;

	if (caa_unlikely(!ht->split_count))
		return;
	index = ht_get_split_count_index(hash);
	split_count = uatomic_add_return(&ht->split_count[index].del, 1);
	if (caa_unlikely(!(split_count & ((1UL << COUNT_COMMIT_ORDER) - 1)))) {
		long count;

		dbg_printf("del split count %lu\n", split_count);
		count = uatomic_add_return(&ht->count,
					   -(1UL << COUNT_COMMIT_ORDER));
		/* If power of 2 */
		if (!(count & (count - 1))) {
			if ((count >> CHAIN_LEN_RESIZE_THRESHOLD) >= size)
				return;
			dbg_printf("del set global %ld\n", count);
			/*
			 * Don't shrink table if the number of nodes is below a
			 * certain threshold.
			 */
			if (count < (1UL << COUNT_COMMIT_ORDER) * (split_count_mask + 1))
				return;
			cds_lfht_resize_lazy_count(ht, size,
				count >> (CHAIN_LEN_TARGET - 1));
		}
	}
}

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
		cds_lfht_resize_lazy_grow(ht, size,
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
int is_bucket(struct cds_lfht_node *node)
{
	return ((unsigned long) node) & BUCKET_FLAG;
}

static
struct cds_lfht_node *flag_bucket(struct cds_lfht_node *node)
{
	return (struct cds_lfht_node *) (((unsigned long) node) | BUCKET_FLAG);
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
unsigned long _uatomic_xchg_monotonic_increase(unsigned long *ptr,
		unsigned long v)
{
	unsigned long old1, old2;

	old1 = uatomic_read(ptr);
	do {
		old2 = old1;
		if (old2 >= v)
			return old2;
	} while ((old1 = uatomic_cmpxchg(ptr, old2, v)) != old2);
	return old2;
}

static inline
struct cds_lfht_node *bucket_at(struct cds_lfht *ht, unsigned long index)
{
	unsigned long order;

	if ((__builtin_constant_p(index) && index == 0)
			|| index < ht->min_alloc_size) {
		dbg_printf("bucket index %lu order 0 aridx 0\n", index);
		return &ht->t.tbl[0]->nodes[index];
	}
	/*
	 * equivalent to get_count_order_ulong(index + 1), but optimizes
	 * away the non-existing 0 special-case for
	 * get_count_order_ulong.
	 */
	order = fls_ulong(index);
	dbg_printf("bucket index %lu order %lu aridx %lu\n",
		   index, order, index & ((1UL << (order - 1)) - 1));
	return &ht->t.tbl[order]->nodes[index & ((1UL << (order - 1)) - 1)];
}

static inline
struct cds_lfht_node *lookup_bucket(struct cds_lfht *ht, unsigned long size,
		unsigned long hash)
{
	assert(size > 0);
	return bucket_at(ht, hash & (size - 1));
}

/*
 * Remove all logically deleted nodes from a bucket up to a certain node key.
 */
static
void _cds_lfht_gc_bucket(struct cds_lfht_node *bucket, struct cds_lfht_node *node)
{
	struct cds_lfht_node *iter_prev, *iter, *next, *new_next;

	assert(!is_bucket(bucket));
	assert(!is_removed(bucket));
	assert(!is_bucket(node));
	assert(!is_removed(node));
	for (;;) {
		iter_prev = bucket;
		/* We can always skip the bucket node initially */
		iter = rcu_dereference(iter_prev->next);
		assert(!is_removed(iter));
		assert(iter_prev->reverse_hash <= node->reverse_hash);
		/*
		 * We should never be called with bucket (start of chain)
		 * and logically removed node (end of path compression
		 * marker) being the actual same node. This would be a
		 * bug in the algorithm implementation.
		 */
		assert(bucket != node);
		for (;;) {
			if (caa_unlikely(is_end(iter)))
				return;
			if (caa_likely(clear_flag(iter)->reverse_hash > node->reverse_hash))
				return;
			next = rcu_dereference(clear_flag(iter)->next);
			if (caa_likely(is_removed(next)))
				break;
			iter_prev = clear_flag(iter);
			iter = next;
		}
		assert(!is_removed(iter));
		if (is_bucket(iter))
			new_next = flag_bucket(clear_flag(next));
		else
			new_next = clear_flag(next);
		(void) uatomic_cmpxchg(&iter_prev->next, iter, new_next);
	}
	return;
}

static
int _cds_lfht_replace(struct cds_lfht *ht, unsigned long size,
		struct cds_lfht_node *old_node,
		struct cds_lfht_node *old_next,
		struct cds_lfht_node *new_node)
{
	struct cds_lfht_node *bucket, *ret_next;

	if (!old_node)	/* Return -ENOENT if asked to replace NULL node */
		return -ENOENT;

	assert(!is_removed(old_node));
	assert(!is_bucket(old_node));
	assert(!is_removed(new_node));
	assert(!is_bucket(new_node));
	assert(new_node != old_node);
	for (;;) {
		/* Insert after node to be replaced */
		if (is_removed(old_next)) {
			/*
			 * Too late, the old node has been removed under us
			 * between lookup and replace. Fail.
			 */
			return -ENOENT;
		}
		assert(!is_bucket(old_next));
		assert(new_node != clear_flag(old_next));
		new_node->next = clear_flag(old_next);
		/*
		 * Here is the whole trick for lock-free replace: we add
		 * the replacement node _after_ the node we want to
		 * replace by atomically setting its next pointer at the
		 * same time we set its removal flag. Given that
		 * the lookups/get next use an iterator aware of the
		 * next pointer, they will either skip the old node due
		 * to the removal flag and see the new node, or use
		 * the old node, but will not see the new one.
		 */
		ret_next = uatomic_cmpxchg(&old_node->next,
			      old_next, flag_removed(new_node));
		if (ret_next == old_next)
			break;		/* We performed the replacement. */
		old_next = ret_next;
	}

	/*
	 * Ensure that the old node is not visible to readers anymore:
	 * lookup for the node, and remove it (along with any other
	 * logically removed node) if found.
	 */
	bucket = lookup_bucket(ht, size, bit_reverse_ulong(old_node->reverse_hash));
	_cds_lfht_gc_bucket(bucket, new_node);

	assert(is_removed(rcu_dereference(old_node->next)));
	return 0;
}

/*
 * A non-NULL unique_ret pointer uses the "add unique" (or uniquify) add
 * mode. A NULL unique_ret allows creation of duplicate keys.
 */
static
void _cds_lfht_add(struct cds_lfht *ht,
		cds_lfht_match_fct match,
		const void *key,
		unsigned long size,
		struct cds_lfht_node *node,
		struct cds_lfht_iter *unique_ret,
		int bucket_flag)
{
	struct cds_lfht_node *iter_prev, *iter, *next, *new_node, *new_next,
			*return_node;
	struct cds_lfht_node *bucket;

	assert(!is_bucket(node));
	assert(!is_removed(node));
	bucket = lookup_bucket(ht, size, bit_reverse_ulong(node->reverse_hash));
	for (;;) {
		uint32_t chain_len = 0;

		/*
		 * iter_prev points to the non-removed node prior to the
		 * insert location.
		 */
		iter_prev = bucket;
		/* We can always skip the bucket node initially */
		iter = rcu_dereference(iter_prev->next);
		assert(iter_prev->reverse_hash <= node->reverse_hash);
		for (;;) {
			if (caa_unlikely(is_end(iter)))
				goto insert;
			if (caa_likely(clear_flag(iter)->reverse_hash > node->reverse_hash))
				goto insert;

			/* bucket node is the first node of the identical-hash-value chain */
			if (bucket_flag && clear_flag(iter)->reverse_hash == node->reverse_hash)
				goto insert;

			next = rcu_dereference(clear_flag(iter)->next);
			if (caa_unlikely(is_removed(next)))
				goto gc_node;

			/* uniquely add */
			if (unique_ret
			    && !is_bucket(next)
			    && clear_flag(iter)->reverse_hash == node->reverse_hash) {
				struct cds_lfht_iter d_iter = { .node = node, .next = iter, };

				/*
				 * uniquely adding inserts the node as the first
				 * node of the identical-hash-value node chain.
				 *
				 * This semantic ensures no duplicated keys
				 * should ever be observable in the table
				 * (including observe one node by one node
				 * by forward iterations)
				 */
				cds_lfht_next_duplicate(ht, match, key, &d_iter);
				if (!d_iter.node)
					goto insert;

				*unique_ret = d_iter;
				return;
			}

			/* Only account for identical reverse hash once */
			if (iter_prev->reverse_hash != clear_flag(iter)->reverse_hash
			    && !is_bucket(next))
				check_resize(ht, size, ++chain_len);
			iter_prev = clear_flag(iter);
			iter = next;
		}

	insert:
		assert(node != clear_flag(iter));
		assert(!is_removed(iter_prev));
		assert(!is_removed(iter));
		assert(iter_prev != node);
		if (!bucket_flag)
			node->next = clear_flag(iter);
		else
			node->next = flag_bucket(clear_flag(iter));
		if (is_bucket(iter))
			new_node = flag_bucket(node);
		else
			new_node = node;
		if (uatomic_cmpxchg(&iter_prev->next, iter,
				    new_node) != iter) {
			continue;	/* retry */
		} else {
			return_node = node;
			goto end;
		}

	gc_node:
		assert(!is_removed(iter));
		if (is_bucket(iter))
			new_next = flag_bucket(clear_flag(next));
		else
			new_next = clear_flag(next);
		(void) uatomic_cmpxchg(&iter_prev->next, iter, new_next);
		/* retry */
	}
end:
	if (unique_ret) {
		unique_ret->node = return_node;
		/* unique_ret->next left unset, never used. */
	}
}

static
int _cds_lfht_del(struct cds_lfht *ht, unsigned long size,
		struct cds_lfht_node *node,
		int bucket_removal)
{
	struct cds_lfht_node *bucket, *next, *old;

	if (!node)	/* Return -ENOENT if asked to delete NULL node */
		return -ENOENT;

	/* logically delete the node */
	assert(!is_bucket(node));
	assert(!is_removed(node));
	old = rcu_dereference(node->next);
	do {
		struct cds_lfht_node *new_next;

		next = old;
		if (caa_unlikely(is_removed(next)))
			return -ENOENT;
		if (bucket_removal)
			assert(is_bucket(next));
		else
			assert(!is_bucket(next));
		new_next = flag_removed(next);
		old = uatomic_cmpxchg(&node->next, next, new_next);
	} while (old != next);
	/* We performed the (logical) deletion. */

	/*
	 * Ensure that the node is not visible to readers anymore: lookup for
	 * the node, and remove it (along with any other logically removed node)
	 * if found.
	 */
	bucket = lookup_bucket(ht, size, bit_reverse_ulong(node->reverse_hash));
	_cds_lfht_gc_bucket(bucket, node);

	assert(is_removed(rcu_dereference(node->next)));
	return 0;
}

static
void *partition_resize_thread(void *arg)
{
	struct partition_resize_work *work = arg;

	work->ht->cds_lfht_rcu_register_thread();
	work->fct(work->ht, work->i, work->start, work->len);
	work->ht->cds_lfht_rcu_unregister_thread();
	return NULL;
}

static
void partition_resize_helper(struct cds_lfht *ht, unsigned long i,
		unsigned long len,
		void (*fct)(struct cds_lfht *ht, unsigned long i,
			unsigned long start, unsigned long len))
{
	unsigned long partition_len;
	struct partition_resize_work *work;
	int thread, ret;
	unsigned long nr_threads;

	/*
	 * Note: nr_cpus_mask + 1 is always power of 2.
	 * We spawn just the number of threads we need to satisfy the minimum
	 * partition size, up to the number of CPUs in the system.
	 */
	if (nr_cpus_mask > 0) {
		nr_threads = min(nr_cpus_mask + 1,
				 len >> MIN_PARTITION_PER_THREAD_ORDER);
	} else {
		nr_threads = 1;
	}
	partition_len = len >> get_count_order_ulong(nr_threads);
	work = calloc(nr_threads, sizeof(*work));
	assert(work);
	for (thread = 0; thread < nr_threads; thread++) {
		work[thread].ht = ht;
		work[thread].i = i;
		work[thread].len = partition_len;
		work[thread].start = thread * partition_len;
		work[thread].fct = fct;
		ret = pthread_create(&(work[thread].thread_id), ht->resize_attr,
			partition_resize_thread, &work[thread]);
		assert(!ret);
	}
	for (thread = 0; thread < nr_threads; thread++) {
		ret = pthread_join(work[thread].thread_id, NULL);
		assert(!ret);
	}
	free(work);
}

/*
 * Holding RCU read lock to protect _cds_lfht_add against memory
 * reclaim that could be performed by other call_rcu worker threads (ABA
 * problem).
 *
 * When we reach a certain length, we can split this population phase over
 * many worker threads, based on the number of CPUs available in the system.
 * This should therefore take care of not having the expand lagging behind too
 * many concurrent insertion threads by using the scheduler's ability to
 * schedule bucket node population fairly with insertions.
 */
static
void init_table_populate_partition(struct cds_lfht *ht, unsigned long i,
				   unsigned long start, unsigned long len)
{
	unsigned long j, size = 1UL << (i - 1);

	assert(i > ht->min_alloc_order);
	ht->cds_lfht_rcu_read_lock();
	for (j = size + start; j < size + start + len; j++) {
		struct cds_lfht_node *new_node = bucket_at(ht, j);

		assert(j >= size && j < (size << 1));
		dbg_printf("init populate: order %lu index %lu hash %lu\n",
			   i, j, j);
		new_node->reverse_hash = bit_reverse_ulong(j);
		_cds_lfht_add(ht, NULL, NULL, size, new_node, NULL, 1);
	}
	ht->cds_lfht_rcu_read_unlock();
}

static
void init_table_populate(struct cds_lfht *ht, unsigned long i,
			 unsigned long len)
{
	assert(nr_cpus_mask != -1);
	if (nr_cpus_mask < 0 || len < 2 * MIN_PARTITION_PER_THREAD) {
		ht->cds_lfht_rcu_thread_online();
		init_table_populate_partition(ht, i, 0, len);
		ht->cds_lfht_rcu_thread_offline();
		return;
	}
	partition_resize_helper(ht, i, len, init_table_populate_partition);
}

static
void init_table(struct cds_lfht *ht,
		unsigned long first_order, unsigned long last_order)
{
	unsigned long i;

	dbg_printf("init table: first_order %lu last_order %lu\n",
		   first_order, last_order);
	assert(first_order > ht->min_alloc_order);
	for (i = first_order; i <= last_order; i++) {
		unsigned long len;

		len = 1UL << (i - 1);
		dbg_printf("init order %lu len: %lu\n", i, len);

		/* Stop expand if the resize target changes under us */
		if (CMM_LOAD_SHARED(ht->t.resize_target) < (1UL << i))
			break;

		ht->t.tbl[i] = calloc(1, len * sizeof(struct cds_lfht_node));
		assert(ht->t.tbl[i]);

		/*
		 * Set all bucket nodes reverse hash values for a level and
		 * link all bucket nodes into the table.
		 */
		init_table_populate(ht, i, len);

		/*
		 * Update table size.
		 */
		cmm_smp_wmb();	/* populate data before RCU size */
		CMM_STORE_SHARED(ht->t.size, 1UL << i);

		dbg_printf("init new size: %lu\n", 1UL << i);
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
 * invoked to free a hole level of bucket nodes (after a grace period).
 *
 * Logical removal and garbage collection can therefore be done in batch or on a
 * node-per-node basis, as long as the guarantee above holds.
 *
 * When we reach a certain length, we can split this removal over many worker
 * threads, based on the number of CPUs available in the system. This should
 * take care of not letting resize process lag behind too many concurrent
 * updater threads actively inserting into the hash table.
 */
static
void remove_table_partition(struct cds_lfht *ht, unsigned long i,
			    unsigned long start, unsigned long len)
{
	unsigned long j, size = 1UL << (i - 1);

	assert(i > ht->min_alloc_order);
	ht->cds_lfht_rcu_read_lock();
	for (j = size + start; j < size + start + len; j++) {
		struct cds_lfht_node *fini_node = bucket_at(ht, j);

		assert(j >= size && j < (size << 1));
		dbg_printf("remove entry: order %lu index %lu hash %lu\n",
			   i, j, j);
		fini_node->reverse_hash = bit_reverse_ulong(j);
		(void) _cds_lfht_del(ht, size, fini_node, 1);
	}
	ht->cds_lfht_rcu_read_unlock();
}

static
void remove_table(struct cds_lfht *ht, unsigned long i, unsigned long len)
{

	assert(nr_cpus_mask != -1);
	if (nr_cpus_mask < 0 || len < 2 * MIN_PARTITION_PER_THREAD) {
		ht->cds_lfht_rcu_thread_online();
		remove_table_partition(ht, i, 0, len);
		ht->cds_lfht_rcu_thread_offline();
		return;
	}
	partition_resize_helper(ht, i, len, remove_table_partition);
}

static
void fini_table(struct cds_lfht *ht,
		unsigned long first_order, unsigned long last_order)
{
	long i;
	void *free_by_rcu = NULL;

	dbg_printf("fini table: first_order %lu last_order %lu\n",
		   first_order, last_order);
	assert(first_order > ht->min_alloc_order);
	for (i = last_order; i >= first_order; i--) {
		unsigned long len;

		len = 1UL << (i - 1);
		dbg_printf("fini order %lu len: %lu\n", i, len);

		/* Stop shrink if the resize target changes under us */
		if (CMM_LOAD_SHARED(ht->t.resize_target) > (1UL << (i - 1)))
			break;

		cmm_smp_wmb();	/* populate data before RCU size */
		CMM_STORE_SHARED(ht->t.size, 1UL << (i - 1));

		/*
		 * We need to wait for all add operations to reach Q.S. (and
		 * thus use the new table for lookups) before we can start
		 * releasing the old bucket nodes. Otherwise their lookup will
		 * return a logically removed node as insert position.
		 */
		ht->cds_lfht_synchronize_rcu();
		if (free_by_rcu)
			free(free_by_rcu);

		/*
		 * Set "removed" flag in bucket nodes about to be removed.
		 * Unlink all now-logically-removed bucket node pointers.
		 * Concurrent add/remove operation are helping us doing
		 * the gc.
		 */
		remove_table(ht, i, len);

		free_by_rcu = ht->t.tbl[i];

		dbg_printf("fini new size: %lu\n", 1UL << i);
		if (CMM_LOAD_SHARED(ht->in_progress_destroy))
			break;
	}

	if (free_by_rcu) {
		ht->cds_lfht_synchronize_rcu();
		free(free_by_rcu);
	}
}

static
void cds_lfht_create_bucket(struct cds_lfht *ht, unsigned long size)
{
	struct cds_lfht_node *prev, *node;
	unsigned long order, len, i;

	ht->t.tbl[0] = calloc(1, ht->min_alloc_size * sizeof(struct cds_lfht_node));
	assert(ht->t.tbl[0]);

	dbg_printf("create bucket: order 0 index 0 hash 0\n");
	node = bucket_at(ht, 0);
	node->next = flag_bucket(get_end());
	node->reverse_hash = 0;

	for (order = 1; order < get_count_order_ulong(size) + 1; order++) {
		len = 1UL << (order - 1);
		if (order <= ht->min_alloc_order) {
			ht->t.tbl[order] = (struct rcu_level *) (ht->t.tbl[0]->nodes + len);
		} else {
			ht->t.tbl[order] = calloc(1, len * sizeof(struct cds_lfht_node));
			assert(ht->t.tbl[order]);
		}

		for (i = 0; i < len; i++) {
			/*
			 * Now, we are trying to init the node with the
			 * hash=(len+i) (which is also a bucket with the
			 * index=(len+i)) and insert it into the hash table,
			 * so this node has to be inserted after the bucket
			 * with the index=(len+i)&(len-1)=i. And because there
			 * is no other non-bucket node nor bucket node with
			 * larger index/hash inserted, so the bucket node
			 * being inserted should be inserted directly linked
			 * after the bucket node with index=i.
			 */
			prev = bucket_at(ht, i);
			node = bucket_at(ht, len + i);

			dbg_printf("create bucket: order %lu index %lu hash %lu\n",
				   order, len + i, len + i);
			node->reverse_hash = bit_reverse_ulong(len + i);

			/* insert after prev */
			assert(is_bucket(prev->next));
			node->next = prev->next;
			prev->next = flag_bucket(node);
		}
	}
}

struct cds_lfht *_cds_lfht_new(unsigned long init_size,
			unsigned long min_alloc_size,
			int flags,
			void (*cds_lfht_call_rcu)(struct rcu_head *head,
					void (*func)(struct rcu_head *head)),
			void (*cds_lfht_synchronize_rcu)(void),
			void (*cds_lfht_rcu_read_lock)(void),
			void (*cds_lfht_rcu_read_unlock)(void),
			void (*cds_lfht_rcu_thread_offline)(void),
			void (*cds_lfht_rcu_thread_online)(void),
			void (*cds_lfht_rcu_register_thread)(void),
			void (*cds_lfht_rcu_unregister_thread)(void),
			pthread_attr_t *attr)
{
	struct cds_lfht *ht;
	unsigned long order;

	/* min_alloc_size must be power of two */
	if (!min_alloc_size || (min_alloc_size & (min_alloc_size - 1)))
		return NULL;
	/* init_size must be power of two */
	if (!init_size || (init_size & (init_size - 1)))
		return NULL;
	min_alloc_size = max(min_alloc_size, MIN_TABLE_SIZE);
	init_size = max(init_size, min_alloc_size);
	ht = calloc(1, sizeof(struct cds_lfht));
	assert(ht);
	ht->flags = flags;
	ht->cds_lfht_call_rcu = cds_lfht_call_rcu;
	ht->cds_lfht_synchronize_rcu = cds_lfht_synchronize_rcu;
	ht->cds_lfht_rcu_read_lock = cds_lfht_rcu_read_lock;
	ht->cds_lfht_rcu_read_unlock = cds_lfht_rcu_read_unlock;
	ht->cds_lfht_rcu_thread_offline = cds_lfht_rcu_thread_offline;
	ht->cds_lfht_rcu_thread_online = cds_lfht_rcu_thread_online;
	ht->cds_lfht_rcu_register_thread = cds_lfht_rcu_register_thread;
	ht->cds_lfht_rcu_unregister_thread = cds_lfht_rcu_unregister_thread;
	ht->resize_attr = attr;
	alloc_split_items_count(ht);
	/* this mutex should not nest in read-side C.S. */
	pthread_mutex_init(&ht->resize_mutex, NULL);
	order = get_count_order_ulong(init_size);
	ht->t.resize_target = 1UL << order;
	ht->min_alloc_size = min_alloc_size;
	ht->min_alloc_order = get_count_order_ulong(min_alloc_size);
	cds_lfht_create_bucket(ht, 1UL << order);
	ht->t.size = 1UL << order;
	return ht;
}

void cds_lfht_lookup(struct cds_lfht *ht, unsigned long hash,
		cds_lfht_match_fct match, const void *key,
		struct cds_lfht_iter *iter)
{
	struct cds_lfht_node *node, *next, *bucket;
	unsigned long reverse_hash, size;

	reverse_hash = bit_reverse_ulong(hash);

	size = rcu_dereference(ht->t.size);
	bucket = lookup_bucket(ht, size, hash);
	/* We can always skip the bucket node initially */
	node = rcu_dereference(bucket->next);
	node = clear_flag(node);
	for (;;) {
		if (caa_unlikely(is_end(node))) {
			node = next = NULL;
			break;
		}
		if (caa_unlikely(node->reverse_hash > reverse_hash)) {
			node = next = NULL;
			break;
		}
		next = rcu_dereference(node->next);
		assert(node == clear_flag(node));
		if (caa_likely(!is_removed(next))
		    && !is_bucket(next)
		    && node->reverse_hash == reverse_hash
		    && caa_likely(match(node, key))) {
				break;
		}
		node = clear_flag(next);
	}
	assert(!node || !is_bucket(rcu_dereference(node->next)));
	iter->node = node;
	iter->next = next;
}

void cds_lfht_next_duplicate(struct cds_lfht *ht, cds_lfht_match_fct match,
		const void *key, struct cds_lfht_iter *iter)
{
	struct cds_lfht_node *node, *next;
	unsigned long reverse_hash;

	node = iter->node;
	reverse_hash = node->reverse_hash;
	next = iter->next;
	node = clear_flag(next);

	for (;;) {
		if (caa_unlikely(is_end(node))) {
			node = next = NULL;
			break;
		}
		if (caa_unlikely(node->reverse_hash > reverse_hash)) {
			node = next = NULL;
			break;
		}
		next = rcu_dereference(node->next);
		if (caa_likely(!is_removed(next))
		    && !is_bucket(next)
		    && caa_likely(match(node, key))) {
				break;
		}
		node = clear_flag(next);
	}
	assert(!node || !is_bucket(rcu_dereference(node->next)));
	iter->node = node;
	iter->next = next;
}

void cds_lfht_next(struct cds_lfht *ht, struct cds_lfht_iter *iter)
{
	struct cds_lfht_node *node, *next;

	node = clear_flag(iter->next);
	for (;;) {
		if (caa_unlikely(is_end(node))) {
			node = next = NULL;
			break;
		}
		next = rcu_dereference(node->next);
		if (caa_likely(!is_removed(next))
		    && !is_bucket(next)) {
				break;
		}
		node = clear_flag(next);
	}
	assert(!node || !is_bucket(rcu_dereference(node->next)));
	iter->node = node;
	iter->next = next;
}

void cds_lfht_first(struct cds_lfht *ht, struct cds_lfht_iter *iter)
{
	/*
	 * Get next after first bucket node. The first bucket node is the
	 * first node of the linked list.
	 */
	iter->next = bucket_at(ht, 0)->next;
	cds_lfht_next(ht, iter);
}

void cds_lfht_add(struct cds_lfht *ht, unsigned long hash,
		struct cds_lfht_node *node)
{
	unsigned long size;

	node->reverse_hash = bit_reverse_ulong((unsigned long) hash);
	size = rcu_dereference(ht->t.size);
	_cds_lfht_add(ht, NULL, NULL, size, node, NULL, 0);
	ht_count_add(ht, size, hash);
}

struct cds_lfht_node *cds_lfht_add_unique(struct cds_lfht *ht,
				unsigned long hash,
				cds_lfht_match_fct match,
				const void *key,
				struct cds_lfht_node *node)
{
	unsigned long size;
	struct cds_lfht_iter iter;

	node->reverse_hash = bit_reverse_ulong((unsigned long) hash);
	size = rcu_dereference(ht->t.size);
	_cds_lfht_add(ht, match, key, size, node, &iter, 0);
	if (iter.node == node)
		ht_count_add(ht, size, hash);
	return iter.node;
}

struct cds_lfht_node *cds_lfht_add_replace(struct cds_lfht *ht,
				unsigned long hash,
				cds_lfht_match_fct match,
				const void *key,
				struct cds_lfht_node *node)
{
	unsigned long size;
	struct cds_lfht_iter iter;

	node->reverse_hash = bit_reverse_ulong((unsigned long) hash);
	size = rcu_dereference(ht->t.size);
	for (;;) {
		_cds_lfht_add(ht, match, key, size, node, &iter, 0);
		if (iter.node == node) {
			ht_count_add(ht, size, hash);
			return NULL;
		}

		if (!_cds_lfht_replace(ht, size, iter.node, iter.next, node))
			return iter.node;
	}
}

int cds_lfht_replace(struct cds_lfht *ht, struct cds_lfht_iter *old_iter,
		struct cds_lfht_node *new_node)
{
	unsigned long size;

	size = rcu_dereference(ht->t.size);
	return _cds_lfht_replace(ht, size, old_iter->node, old_iter->next,
			new_node);
}

int cds_lfht_del(struct cds_lfht *ht, struct cds_lfht_iter *iter)
{
	unsigned long size, hash;
	int ret;

	size = rcu_dereference(ht->t.size);
	ret = _cds_lfht_del(ht, size, iter->node, 0);
	if (!ret) {
		hash = bit_reverse_ulong(iter->node->reverse_hash);
		ht_count_del(ht, size, hash);
	}
	return ret;
}

static
int cds_lfht_delete_bucket(struct cds_lfht *ht)
{
	struct cds_lfht_node *node;
	unsigned long order, i, size;

	/* Check that the table is empty */
	node = bucket_at(ht, 0);
	do {
		node = clear_flag(node)->next;
		if (!is_bucket(node))
			return -EPERM;
		assert(!is_removed(node));
	} while (!is_end(node));
	/*
	 * size accessed without rcu_dereference because hash table is
	 * being destroyed.
	 */
	size = ht->t.size;
	/* Internal sanity check: all nodes left should be bucket */
	for (order = 0; order < get_count_order_ulong(size) + 1; order++) {
		unsigned long len;

		len = !order ? 1 : 1UL << (order - 1);
		for (i = 0; i < len; i++) {
			dbg_printf("delete order %lu i %lu hash %lu\n",
				order, i,
				bit_reverse_ulong(ht->t.tbl[order]->nodes[i].reverse_hash));
			assert(is_bucket(ht->t.tbl[order]->nodes[i].next));
		}

		if (order == ht->min_alloc_order)
			poison_free(ht->t.tbl[0]);
		else if (order > ht->min_alloc_order)
			poison_free(ht->t.tbl[order]);
		/* Nothing to delete for order < ht->min_alloc_order */
	}
	return 0;
}

/*
 * Should only be called when no more concurrent readers nor writers can
 * possibly access the table.
 */
int cds_lfht_destroy(struct cds_lfht *ht, pthread_attr_t **attr)
{
	int ret;

	/* Wait for in-flight resize operations to complete */
	_CMM_STORE_SHARED(ht->in_progress_destroy, 1);
	cmm_smp_mb();	/* Store destroy before load resize */
	while (uatomic_read(&ht->in_progress_resize))
		poll(NULL, 0, 100);	/* wait for 100ms */
	ret = cds_lfht_delete_bucket(ht);
	if (ret)
		return ret;
	free_split_items_count(ht);
	if (attr)
		*attr = ht->resize_attr;
	poison_free(ht);
	return ret;
}

void cds_lfht_count_nodes(struct cds_lfht *ht,
		long *approx_before,
		unsigned long *count,
		unsigned long *removed,
		long *approx_after)
{
	struct cds_lfht_node *node, *next;
	unsigned long nr_bucket = 0;

	*approx_before = 0;
	if (ht->split_count) {
		int i;

		for (i = 0; i < split_count_mask + 1; i++) {
			*approx_before += uatomic_read(&ht->split_count[i].add);
			*approx_before -= uatomic_read(&ht->split_count[i].del);
		}
	}

	*count = 0;
	*removed = 0;

	/* Count non-bucket nodes in the table */
	node = bucket_at(ht, 0);
	do {
		next = rcu_dereference(node->next);
		if (is_removed(next)) {
			if (!is_bucket(next))
				(*removed)++;
			else
				(nr_bucket)++;
		} else if (!is_bucket(next))
			(*count)++;
		else
			(nr_bucket)++;
		node = clear_flag(next);
	} while (!is_end(node));
	dbg_printf("number of bucket nodes: %lu\n", nr_bucket);
	*approx_after = 0;
	if (ht->split_count) {
		int i;

		for (i = 0; i < split_count_mask + 1; i++) {
			*approx_after += uatomic_read(&ht->split_count[i].add);
			*approx_after -= uatomic_read(&ht->split_count[i].del);
		}
	}
}

/* called with resize mutex held */
static
void _do_cds_lfht_grow(struct cds_lfht *ht,
		unsigned long old_size, unsigned long new_size)
{
	unsigned long old_order, new_order;

	old_order = get_count_order_ulong(old_size);
	new_order = get_count_order_ulong(new_size);
	dbg_printf("resize from %lu (order %lu) to %lu (order %lu) buckets\n",
		   old_size, old_order, new_size, new_order);
	assert(new_size > old_size);
	init_table(ht, old_order + 1, new_order);
}

/* called with resize mutex held */
static
void _do_cds_lfht_shrink(struct cds_lfht *ht,
		unsigned long old_size, unsigned long new_size)
{
	unsigned long old_order, new_order;

	new_size = max(new_size, ht->min_alloc_size);
	old_order = get_count_order_ulong(old_size);
	new_order = get_count_order_ulong(new_size);
	dbg_printf("resize from %lu (order %lu) to %lu (order %lu) buckets\n",
		   old_size, old_order, new_size, new_order);
	assert(new_size < old_size);

	/* Remove and unlink all bucket nodes to remove. */
	fini_table(ht, new_order + 1, old_order);
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
		assert(uatomic_read(&ht->in_progress_resize));
		if (CMM_LOAD_SHARED(ht->in_progress_destroy))
			break;
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
unsigned long resize_target_grow(struct cds_lfht *ht, unsigned long new_size)
{
	return _uatomic_xchg_monotonic_increase(&ht->t.resize_target, new_size);
}

static
void resize_target_update_count(struct cds_lfht *ht,
				unsigned long count)
{
	count = max(count, ht->min_alloc_size);
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
void __cds_lfht_resize_lazy_launch(struct cds_lfht *ht)
{
	struct rcu_resize_work *work;

	/* Store resize_target before read resize_initiated */
	cmm_smp_mb();
	if (!CMM_LOAD_SHARED(ht->t.resize_initiated)) {
		uatomic_inc(&ht->in_progress_resize);
		cmm_smp_mb();	/* increment resize count before load destroy */
		if (CMM_LOAD_SHARED(ht->in_progress_destroy)) {
			uatomic_dec(&ht->in_progress_resize);
			return;
		}
		work = malloc(sizeof(*work));
		work->ht = ht;
		ht->cds_lfht_call_rcu(&work->head, do_resize_cb);
		CMM_STORE_SHARED(ht->t.resize_initiated, 1);
	}
}

static
void cds_lfht_resize_lazy_grow(struct cds_lfht *ht, unsigned long size, int growth)
{
	unsigned long target_size = size << growth;

	if (resize_target_grow(ht, target_size) >= target_size)
		return;

	__cds_lfht_resize_lazy_launch(ht);
}

/*
 * We favor grow operations over shrink. A shrink operation never occurs
 * if a grow operation is queued for lazy execution. A grow operation
 * cancels any pending shrink lazy execution.
 */
static
void cds_lfht_resize_lazy_count(struct cds_lfht *ht, unsigned long size,
				unsigned long count)
{
	if (!(ht->flags & CDS_LFHT_AUTO_RESIZE))
		return;
	count = max(count, ht->min_alloc_size);
	if (count == size)
		return;		/* Already the right size, no resize needed */
	if (count > size) {	/* lazy grow */
		if (resize_target_grow(ht, count) >= count)
			return;
	} else {		/* lazy shrink */
		for (;;) {
			unsigned long s;

			s = uatomic_cmpxchg(&ht->t.resize_target, size, count);
			if (s == size)
				break;	/* no resize needed */
			if (s > size)
				return;	/* growing is/(was just) in progress */
			if (s <= count)
				return;	/* some other thread do shrink */
			size = s;
		}
	}
	__cds_lfht_resize_lazy_launch(ht);
}
