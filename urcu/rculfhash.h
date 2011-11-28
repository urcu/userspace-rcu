#ifndef _URCU_RCULFHASH_H
#define _URCU_RCULFHASH_H

/*
 * urcu/rculfhash.h
 *
 * Userspace RCU library - Lock-Free RCU Hash Table
 *
 * Copyright 2011 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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
 *
 * Include this file _after_ including your URCU flavor.
 */

#include <stdint.h>
#include <urcu/compiler.h>
#include <urcu-call-rcu.h>
#include <urcu-flavor.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * cds_lfht_node: Contains the next pointers and reverse-hash
 * value required for lookup and traversal of the hash table.
 *
 * struct cds_lfht_node should be aligned on 4-bytes boundaries because
 * the two lower bits are used as flags.
 *
 * struct cds_lfht_node can be embedded into a structure (as a field).
 * caa_container_of() can be used to get the structure from the struct
 * cds_lfht_node after a lookup.
 *
 * The structure which embeds it typically holds the key (or key-value
 * pair) of the object. The caller code is responsible for calculation
 * of the hash value for cds_lfht APIs.
 */
struct cds_lfht_node {
	struct cds_lfht_node *next;	/* ptr | BUCKET_FLAG | REMOVED_FLAG */
	unsigned long reverse_hash;
} __attribute__((aligned(4)));

/* cds_lfht_iter: Used to track state while traversing a hash chain. */
struct cds_lfht_iter {
	struct cds_lfht_node *node, *next;
};

static inline
struct cds_lfht_node *cds_lfht_iter_get_node(struct cds_lfht_iter *iter)
{
	return iter->node;
}

struct cds_lfht;

/*
 * Caution !
 * Ensure reader and writer threads are registered as urcu readers.
 */

typedef int (*cds_lfht_match_fct)(struct cds_lfht_node *node, const void *key);

/*
 * cds_lfht_node_init - initialize a hash table node
 * @node: the node to initialize.
 *
 * This function is kept to be eventually used for debugging purposes
 * (detection of memory corruption).
 */
static inline
void cds_lfht_node_init(struct cds_lfht_node *node)
{
}

/*
 * Hash table creation flags.
 */
enum {
	CDS_LFHT_AUTO_RESIZE = (1U << 0),
	CDS_LFHT_ACCOUNTING = (1U << 1),
};

struct cds_lfht_mm_type {
	struct cds_lfht *(*alloc_cds_lfht)(unsigned long min_nr_alloc_buckets,
			unsigned long max_nr_buckets);
	void (*alloc_bucket_table)(struct cds_lfht *ht, unsigned long order);
	void (*free_bucket_table)(struct cds_lfht *ht, unsigned long order);
	struct cds_lfht_node *(*bucket_at)(struct cds_lfht *ht,
			unsigned long index);
};

extern const struct cds_lfht_mm_type cds_lfht_mm_order;
extern const struct cds_lfht_mm_type cds_lfht_mm_chunk;
extern const struct cds_lfht_mm_type cds_lfht_mm_mmap;

/*
 * _cds_lfht_new - API used by cds_lfht_new wrapper. Do not use directly.
 */
struct cds_lfht *_cds_lfht_new(unsigned long init_size,
			unsigned long min_nr_alloc_buckets,
			unsigned long max_nr_buckets,
			int flags,
			const struct cds_lfht_mm_type *mm,
			const struct rcu_flavor_struct *flavor,
			pthread_attr_t *attr);

/*
 * cds_lfht_new - allocate a hash table.
 * @init_size: number of buckets to allocate initially. Must be power of two.
 * @min_nr_alloc_buckets: the minimum number of allocated buckets.
 *                        (must be power of two)
 * @max_nr_buckets: the maximum number of hash table buckets allowed.
 *                  (must be power of two)
 * @flags: hash table creation flags (can be combined with bitwise or: '|').
 *           0: no flags.
 *           CDS_LFHT_AUTO_RESIZE: automatically resize hash table.
 *           CDS_LFHT_ACCOUNTING: count the number of node addition
 *                                and removal in the table
 * @attr: optional resize worker thread attributes. NULL for default.
 *
 * Return NULL on error.
 * Note: the RCU flavor must be already included before the hash table header.
 *
 * The programmer is responsible for ensuring that resize operation has a
 * priority equal to hash table updater threads. It should be performed by
 * specifying the appropriate priority in the pthread "attr" argument, and,
 * for CDS_LFHT_AUTO_RESIZE, by ensuring that call_rcu worker threads also have
 * this priority level. Having lower priority for call_rcu and resize threads
 * does not pose any correctness issue, but the resize operations could be
 * starved by updates, thus leading to long hash table bucket chains.
 * Threads calling this API are NOT required to be registered RCU read-side
 * threads. It can be called very early.(before rcu is initialized ...etc.)
 */
static inline
struct cds_lfht *cds_lfht_new(unsigned long init_size,
			unsigned long min_nr_alloc_buckets,
			unsigned long max_nr_buckets,
			int flags,
			pthread_attr_t *attr)
{
	return _cds_lfht_new(init_size, min_nr_alloc_buckets, max_nr_buckets,
			flags, &cds_lfht_mm_order, &rcu_flavor, attr);
}

/*
 * cds_lfht_destroy - destroy a hash table.
 * @ht: the hash table to destroy.
 * @attr: (output) resize worker thread attributes, as received by cds_lfht_new.
 *        The caller will typically want to free this pointer if dynamically
 *        allocated. The attr point can be NULL if the caller does not
 *        need to be informed of the value passed to cds_lfht_new().
 *
 * Return 0 on success, negative error value on error.
 * Threads calling this API need to be registered RCU read-side threads.
 */
int cds_lfht_destroy(struct cds_lfht *ht, pthread_attr_t **attr);

/*
 * cds_lfht_count_nodes - count the number of nodes in the hash table.
 * @ht: the hash table.
 * @split_count_before: Sample the node count split-counter before traversal.
 * @count: Traverse the hash table, count the number of nodes observed.
 * @removed: Number of logically removed nodes observed during traversal.
 * @split_count_after: Sample the node count split-counter after traversal.
 *
 * Call with rcu_read_lock held.
 * Threads calling this API need to be registered RCU read-side threads.
 */
void cds_lfht_count_nodes(struct cds_lfht *ht,
		long *split_count_before,
		unsigned long *count,
		unsigned long *removed,
		long *split_count_after);

/*
 * cds_lfht_lookup - lookup a node by key.
 * @ht: the hash table.
 * @hash: the key hash.
 * @match: the key match function.
 * @key: the current node key.
 * @iter: Node, if found (output). *iter->node set to NULL if not found.
 *
 * Call with rcu_read_lock held.
 * Threads calling this API need to be registered RCU read-side threads.
 */
void cds_lfht_lookup(struct cds_lfht *ht, unsigned long hash,
		cds_lfht_match_fct match, const void *key,
		struct cds_lfht_iter *iter);

/*
 * cds_lfht_next_duplicate - get the next item with same key (after a lookup).
 * @ht: the hash table.
 * @match: the key match function.
 * @key: the current node key.
 * @iter: Node, if found (output). *iter->node set to NULL if not found.
 *
 * Uses an iterator initialized by a lookup.
 * Sets *iter-node to the following node with same key.
 * Sets *iter->node to NULL if no following node exists with same key.
 * RCU read-side lock must be held across cds_lfht_lookup and
 * cds_lfht_next calls, and also between cds_lfht_next calls using the
 * node returned by a previous cds_lfht_next.
 * Call with rcu_read_lock held.
 * Threads calling this API need to be registered RCU read-side threads.
 */
void cds_lfht_next_duplicate(struct cds_lfht *ht,
		cds_lfht_match_fct match, const void *key,
		struct cds_lfht_iter *iter);

/*
 * cds_lfht_first - get the first node in the table.
 * @ht: the hash table.
 * @iter: First node, if exists (output). *iter->node set to NULL if not found.
 *
 * Output in "*iter". *iter->node set to NULL if table is empty.
 * Call with rcu_read_lock held.
 * Threads calling this API need to be registered RCU read-side threads.
 */
void cds_lfht_first(struct cds_lfht *ht, struct cds_lfht_iter *iter);

/*
 * cds_lfht_next - get the next node in the table.
 * @ht: the hash table.
 * @iter: Next node, if exists (output). *iter->node set to NULL if not found.
 *
 * Input/Output in "*iter". *iter->node set to NULL if *iter was
 * pointing to the last table node.
 * Call with rcu_read_lock held.
 * Threads calling this API need to be registered RCU read-side threads.
 */
void cds_lfht_next(struct cds_lfht *ht, struct cds_lfht_iter *iter);

/*
 * cds_lfht_add - add a node to the hash table.
 * @ht: the hash table.
 * @hash: the key hash.
 * @node: the node to add.
 *
 * This function supports adding redundant keys into the table.
 * Call with rcu_read_lock held.
 * Threads calling this API need to be registered RCU read-side threads.
 */
void cds_lfht_add(struct cds_lfht *ht, unsigned long hash,
		struct cds_lfht_node *node);

/*
 * cds_lfht_add_unique - add a node to hash table, if key is not present.
 * @ht: the hash table.
 * @hash: the node's hash.
 * @match: the key match function.
 * @key: the node's key.
 * @node: the node to try adding.
 *
 * Return the node added upon success.
 * Return the unique node already present upon failure. If
 * cds_lfht_add_unique fails, the node passed as parameter should be
 * freed by the caller.
 * Call with rcu_read_lock held.
 * Threads calling this API need to be registered RCU read-side threads.
 *
 * The semantic of this function is that if only this function is used
 * to add keys into the table, no duplicated keys should ever be
 * observable in the table. The same guarantee apply for combination of
 * add_unique and add_replace (see below).
 */
struct cds_lfht_node *cds_lfht_add_unique(struct cds_lfht *ht,
		unsigned long hash,
		cds_lfht_match_fct match,
		const void *key,
		struct cds_lfht_node *node);

/*
 * cds_lfht_add_replace - replace or add a node within hash table.
 * @ht: the hash table.
 * @hash: the node's hash.
 * @match: the key match function.
 * @key: the node's key.
 * @node: the node to add.
 *
 * Return the node replaced upon success. If no node matching the key
 * was present, return NULL, which also means the operation succeeded.
 * This replacement operation should never fail.
 * Call with rcu_read_lock held.
 * Threads calling this API need to be registered RCU read-side threads.
 * After successful replacement, a grace period must be waited for before
 * freeing the memory reserved for the returned node.
 *
 * The semantic of replacement vs lookups is the following: if lookups
 * are performed between a key unique insertion and its removal, we
 * guarantee that the lookups and get next will always find exactly one
 * instance of the key if it is replaced concurrently with the lookups.
 *
 * Providing this semantic allows us to ensure that replacement-only
 * schemes will never generate duplicated keys. It also allows us to
 * guarantee that a combination of add_replace and add_unique updates
 * will never generate duplicated keys.
 */
struct cds_lfht_node *cds_lfht_add_replace(struct cds_lfht *ht,
		unsigned long hash,
		cds_lfht_match_fct match,
		const void *key,
		struct cds_lfht_node *node);

/*
 * cds_lfht_replace - replace a node pointer to by iter within hash table.
 * @ht: the hash table.
 * @old_iter: the iterator position of the node to replace.
 * @now_node: the new node to try using for replacement.
 *
 * Return 0 if replacement is successful, negative value otherwise.
 * Replacing a NULL old node or an already removed node will fail with a
 * negative value.
 * Old node can be looked up with cds_lfht_lookup and cds_lfht_next.
 * RCU read-side lock must be held between lookup and replacement.
 * Call with rcu_read_lock held.
 * Threads calling this API need to be registered RCU read-side threads.
 * After successful replacement, a grace period must be waited for before
 * freeing the memory reserved for the old node (which can be accessed
 * with cds_lfht_iter_get_node).
 *
 * The semantic of replacement vs lookups is the following: if lookups
 * are performed between a key unique insertion and its removal, we
 * guarantee that the lookups and get next will always find exactly one
 * instance of the key if it is replaced concurrently with the lookups.
 *
 * Providing this semantic allows us to ensure that replacement-only
 * schemes will never generate duplicated keys. It also allows us to
 * guarantee that a combination of add_replace and add_unique updates
 * will never generate duplicated keys.
 */
int cds_lfht_replace(struct cds_lfht *ht, struct cds_lfht_iter *old_iter,
		struct cds_lfht_node *new_node);

/*
 * cds_lfht_del - remove node pointed to by iterator from hash table.
 * @ht: the hash table.
 * @iter: the iterator position of the node to delete.
 *
 * Return 0 if the node is successfully removed, negative value
 * otherwise.
 * Replacing a NULL node or an already removed node will fail with a
 * negative value.
 * Node can be looked up with cds_lfht_lookup and cds_lfht_next.
 * cds_lfht_iter_get_node.
 * RCU read-side lock must be held between lookup and removal.
 * Call with rcu_read_lock held.
 * Threads calling this API need to be registered RCU read-side threads.
 * After successful removal, a grace period must be waited for before
 * freeing the memory reserved for old node (which can be accessed with
 * cds_lfht_iter_get_node).
 */
int cds_lfht_del(struct cds_lfht *ht, struct cds_lfht_iter *iter);

/*
 * cds_lfht_resize - Force a hash table resize
 * @ht: the hash table.
 * @new_size: update to this hash table size.
 *
 * Threads calling this API need to be registered RCU read-side threads.
 */
void cds_lfht_resize(struct cds_lfht *ht, unsigned long new_size);

/*
 * Note: cds_lfht_for_each are safe for element removal during
 * iteration.
 */
#define cds_lfht_for_each(ht, iter, node)				\
	for (cds_lfht_first(ht, iter),					\
			node = cds_lfht_iter_get_node(iter);		\
		node != NULL;						\
		cds_lfht_next(ht, iter),				\
			node = cds_lfht_iter_get_node(iter))

#define cds_lfht_for_each_duplicate(ht, hash, match, key, iter, node)	\
	for (cds_lfht_lookup(ht, hash, match, key, iter),		\
			node = cds_lfht_iter_get_node(iter);		\
		node != NULL;						\
		cds_lfht_next_duplicate(ht, match, key, iter),		\
			node = cds_lfht_iter_get_node(iter))

#define cds_lfht_for_each_entry(ht, iter, pos, member)			\
	for (cds_lfht_first(ht, iter),					\
			pos = caa_container_of(cds_lfht_iter_get_node(iter), \
					typeof(*(pos)), member);	\
		&(pos)->member != NULL;					\
		cds_lfht_next(ht, iter),				\
			pos = caa_container_of(cds_lfht_iter_get_node(iter), \
					typeof(*(pos)), member))

#define cds_lfht_for_each_entry_duplicate(ht, hash, match, key,		\
				iter, pos, member)			\
	for (cds_lfht_lookup(ht, hash, match, key, iter),		\
			pos = caa_container_of(cds_lfht_iter_get_node(iter), \
					typeof(*(pos)), member);	\
		&(pos)->member != NULL;					\
		cds_lfht_next_duplicate(ht, match, key, iter),		\
			pos = caa_container_of(cds_lfht_iter_get_node(iter), \
					typeof(*(pos)), member))

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFHASH_H */
