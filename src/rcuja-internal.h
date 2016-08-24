#ifndef _URCU_RCUJA_INTERNAL_H
#define _URCU_RCUJA_INTERNAL_H

/*
 * rcuja/rcuja-internal.h
 *
 * Userspace RCU library - RCU Judy Array Internal Header
 *
 * Copyright (C) 2000 - 2002 Hewlett-Packard Company
 * Copyright 2012-2013 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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

#include <pthread.h>
#include <stdio.h>
#include <inttypes.h>
#include <unistd.h>
#include <urcu/rculfhash.h>

/*
 * Number of least significant pointer bits reserved to represent the
 * child type.
 */
#define JA_TYPE_BITS	3
#define JA_TYPE_MAX_NR	(1UL << JA_TYPE_BITS)
#define JA_TYPE_MASK	(JA_TYPE_MAX_NR - 1)
#define JA_PTR_MASK	(~JA_TYPE_MASK)

#define JA_ENTRY_PER_NODE	256UL
#define JA_LOG2_BITS_PER_BYTE	3U
#define JA_BITS_PER_BYTE	(1U << JA_LOG2_BITS_PER_BYTE)

#define JA_POOL_1D_MASK	((JA_BITS_PER_BYTE - 1) << JA_TYPE_BITS)
#define JA_POOL_2D_MASK	(JA_POOL_1D_MASK << JA_LOG2_BITS_PER_BYTE)

#define JA_MAX_DEPTH	9	/* Maximum depth, including leafs */

/*
 * Entry for NULL node is at index 8 of the table. It is never encoded
 * in flags.
 */
#define NODE_INDEX_NULL		8

/*
 * Number of removals needed on a fallback node before we try to shrink
 * it.
 */
#define JA_FALLBACK_REMOVAL_COUNT	8

/* Never declared. Opaque type used to store flagged node pointers. */
struct cds_ja_inode_flag;
struct cds_ja_inode;

/*
 * Shadow node contains mutex and call_rcu head associated with a node.
 */
struct cds_ja_shadow_node {
	struct cds_lfht_node ht_node;	/* hash table node */
	struct cds_ja_inode_flag *node_flag;	/* reverse mapping and hash table key */
	/*
	 * mutual exclusion on all nodes belonging to the same tree
	 * position (e.g. both nodes before and after recompaction
	 * use the same lock).
	 */
	pthread_mutex_t *lock;
	unsigned int nr_child;		/* number of children in node */
	struct rcu_head head;		/* for deferred node and shadow node reclaim */
	int fallback_removal_count;	/* removals left keeping fallback */
	int level;			/* level in the tree */
	struct cds_ja *ja;		/* toplevel judy array */
};

struct cds_ja {
	struct cds_ja_inode_flag *root;
	unsigned int tree_depth;
	uint64_t key_max;
	/*
	 * We use a hash table to associate node keys to their
	 * respective shadow node. This helps reducing lookup hot path
	 * cache footprint, especially for very small nodes.
	 */
	struct cds_lfht *ht;
	unsigned long nr_fallback;	/* Number of fallback nodes used */

	/* For debugging */
	unsigned long node_fallback_count_distribution[JA_ENTRY_PER_NODE];
	unsigned long nr_nodes_allocated, nr_nodes_freed;
};

static inline
struct cds_ja_inode_flag *ja_node_flag(struct cds_ja_inode *node,
		unsigned long type)
{
	assert(type < (1UL << JA_TYPE_BITS));
	return (struct cds_ja_inode_flag *) (((unsigned long) node) | type);
}

static inline
struct cds_ja_inode_flag *ja_node_flag_pool_1d(struct cds_ja_inode *node,
		unsigned long type, unsigned long bitsel)
{
	assert(type < (1UL << JA_TYPE_BITS));
	assert(bitsel < JA_BITS_PER_BYTE);
	return (struct cds_ja_inode_flag *) (((unsigned long) node) | (bitsel << JA_TYPE_BITS) | type);
}

static inline
struct cds_ja_inode_flag *ja_node_flag_pool_2d(struct cds_ja_inode *node,
		unsigned long type, unsigned int bitsel[2])
{
	assert(type < (1UL << JA_TYPE_BITS));
	assert(bitsel[0] < JA_BITS_PER_BYTE);
	assert(bitsel[1] < JA_BITS_PER_BYTE);
	return (struct cds_ja_inode_flag *) (((unsigned long) node) | (bitsel[0] << (JA_TYPE_BITS + JA_LOG2_BITS_PER_BYTE)) | (bitsel[1] << JA_TYPE_BITS) | type);
}

static inline
unsigned long ja_node_pool_1d_bitsel(struct cds_ja_inode_flag *node)
{
	return ((unsigned long) node & JA_POOL_1D_MASK) >> JA_TYPE_BITS;
}

static inline
void ja_node_pool_2d_bitsel(struct cds_ja_inode_flag *node, unsigned long *bits)
{
	bits[0] = ((unsigned long) node & JA_POOL_2D_MASK) >> (JA_TYPE_BITS + JA_LOG2_BITS_PER_BYTE);
	bits[1] = ((unsigned long) node & JA_POOL_1D_MASK) >> JA_TYPE_BITS;
}

/* Hardcoded pool indexes for fast path */
#define RCU_JA_POOL_IDX_5	5
#define RCU_JA_POOL_IDX_6	6
static inline
struct cds_ja_inode *ja_node_ptr(struct cds_ja_inode_flag *node)
{
	unsigned long v, type_idx;

	if (!node)
		return NULL;	/* RCU_JA_NULL */
	v = (unsigned long) node;
	type_idx = v & JA_TYPE_MASK;

	switch (type_idx) {
	case RCU_JA_POOL_IDX_5:
		v &= ~(JA_POOL_1D_MASK | JA_TYPE_MASK);
		break;
	case RCU_JA_POOL_IDX_6:
		v &= ~(JA_POOL_2D_MASK | JA_POOL_1D_MASK | JA_TYPE_MASK);
		break;
	default:
		/* RCU_JA_LINEAR or RCU_JA_PIGEON */
		v &= JA_PTR_MASK;
		break;
	}
	return (struct cds_ja_inode *) v;
}

__attribute__((visibility("protected")))
unsigned long ja_node_type(struct cds_ja_inode_flag *node);

__attribute__((visibility("protected")))
void rcuja_free_all_children(struct cds_ja_shadow_node *shadow_node,
		struct cds_ja_inode_flag *node_flag);

__attribute__((visibility("protected")))
struct cds_ja_shadow_node *rcuja_shadow_lookup_lock(struct cds_lfht *ht,
		struct cds_ja_inode_flag *node_flag);

__attribute__((visibility("protected")))
void rcuja_shadow_unlock(struct cds_ja_shadow_node *shadow_node);

__attribute__((visibility("protected")))
struct cds_ja_shadow_node *rcuja_shadow_set(struct cds_lfht *ht,
		struct cds_ja_inode_flag *new_node_flag,
		struct cds_ja_shadow_node *inherit_from,
		struct cds_ja *ja, int level);

/* rcuja_shadow_clear flags */
enum {
	RCUJA_SHADOW_CLEAR_FREE_NODE = (1U << 0),
	RCUJA_SHADOW_CLEAR_FREE_LOCK = (1U << 1),
};

__attribute__((visibility("protected")))
int rcuja_shadow_clear(struct cds_lfht *ht,
		struct cds_ja_inode_flag *node_flag,
		struct cds_ja_shadow_node *shadow_node,
		unsigned int flags);

__attribute__((visibility("protected")))
void rcuja_shadow_prune(struct cds_lfht *ht,
		unsigned int flags);

__attribute__((visibility("protected")))
struct cds_lfht *rcuja_create_ht(const struct rcu_flavor_struct *flavor);

__attribute__((visibility("protected")))
int rcuja_delete_ht(struct cds_lfht *ht);

__attribute__((visibility("protected")))
void free_cds_ja_node(struct cds_ja *ja, struct cds_ja_inode *node);

/*
 * Iterate through duplicates returned by cds_ja_lookup*()
 * Receives a struct cds_ja_node * as parameter, which is used as start
 * of duplicate list and loop cursor.
 */
#define cds_ja_for_each_duplicate(pos)				\
       for (; (pos) != NULL; (pos) = (pos)->next)

//#define DEBUG
//#define DEBUG_COUNTERS

#ifdef __linux__
#include <syscall.h>
#endif

#if defined(_syscall0)
_syscall0(pid_t, gettid)
#elif defined(__NR_gettid)
static inline pid_t gettid(void)
{
	return syscall(__NR_gettid);
}
#else
#warning "use pid as tid"
static inline pid_t gettid(void)
{
	return getpid();
}
#endif

#ifdef DEBUG
#define dbg_printf(fmt, args...)				\
	fprintf(stderr, "[debug rcuja %lu %s()@%s:%u] " fmt,	\
		(unsigned long) gettid(), __func__,		\
		__FILE__, __LINE__, ## args)

#else
#define dbg_printf(fmt, args...)				\
do {								\
	/* do nothing but check printf format */		\
	if (0)							\
		fprintf(stderr, "[debug rcuja %lu %s()@%s:%u] " fmt, \
			(unsigned long) gettid(), __func__,	\
			__FILE__, __LINE__, ## args);		\
} while (0)
#endif

#ifdef DEBUG_COUNTERS
static inline
int ja_debug_counters(void)
{
	return 1;
}
#else
static inline
int ja_debug_counters(void)
{
	return 0;
}
#endif

#endif /* _URCU_RCUJA_INTERNAL_H */
