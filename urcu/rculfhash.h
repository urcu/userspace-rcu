#ifndef _URCU_RCULFHASH_H
#define _URCU_RCULFHASH_H

/*
 * urcu/rculfhash.h
 *
 * Userspace RCU library - Lock-Free RCU Hash Table
 *
 * Copyright 2011 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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
#include <urcu-call-rcu.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * struct cds_lfht_node and struct _cds_lfht_node should be aligned on
 * 4-bytes boundaries because the two lower bits are used as flags.
 */

struct _cds_lfht_node {
	struct cds_lfht_node *next;	/* ptr | DUMMY_FLAG | REMOVED_FLAG */
	unsigned long reverse_hash;
} __attribute__((aligned(4)));

struct cds_lfht_node {
	/* cache-hot for iteration */
	struct _cds_lfht_node p;          /* needs to be first field */
	void *key;
	unsigned int key_len;
	/* cache-cold for iteration */
	struct rcu_head head;
};

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

typedef unsigned long (*cds_lfht_hash_fct)(void *key, size_t length,
					unsigned long seed);
typedef unsigned long (*cds_lfht_compare_fct)(void *key1, size_t key1_len,
					void *key2, size_t key2_len);

/*
 * cds_lfht_node_init - initialize a hash table node
 */
static inline
void cds_lfht_node_init(struct cds_lfht_node *node, void *key,
			size_t key_len)
{
	node->key = key;
	node->key_len = key_len;
}

/*
 * Hash table creation flags.
 */
enum {
	CDS_LFHT_AUTO_RESIZE = (1U << 0),
};

/*
 * _cds_lfht_new - API used by cds_lfht_new wrapper. Do not use directly.
 */
struct cds_lfht *_cds_lfht_new(cds_lfht_hash_fct hash_fct,
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
			void (*cds_lfht_rcu_thread_online)(void),
			void (*cds_lfht_rcu_register_thread)(void),
			void (*cds_lfht_rcu_unregister_thread)(void),
			pthread_attr_t *attr);

/*
 * cds_lfht_new - allocate a hash table.
 * @hash_fct: the hashing function.
 * @compare_fct: the key comparison function.
 * @hash_seed: the seed for hash function.
 * @init_size: number of nodes to allocate initially. Must be power of two.
 * @flags: hash table creation flags (can be combined with bitwise or: '|').
 *           0: no flags.
 *           CDS_LFHT_AUTO_RESIZE: automatically resize hash table.
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
 */
static inline
struct cds_lfht *cds_lfht_new(cds_lfht_hash_fct hash_fct,
			cds_lfht_compare_fct compare_fct,
			unsigned long hash_seed,
			unsigned long init_size,
			int flags,
			pthread_attr_t *attr)
{
	return _cds_lfht_new(hash_fct, compare_fct, hash_seed,
			init_size, flags,
			call_rcu, synchronize_rcu, rcu_read_lock,
			rcu_read_unlock, rcu_thread_offline,
			rcu_thread_online, rcu_register_thread,
			rcu_unregister_thread, attr);
}

/*
 * cds_lfht_destroy - destroy a hash table.
 * @ht: the hash table to destroy.
 * @attr: (output) resize worker thread attributes, as received by cds_lfht_new.
 *        The caller will typically want to free this pointer if dynamically
 *        allocated.
 *
 * Return 0 on success, negative error value on error.
 */
int cds_lfht_destroy(struct cds_lfht *ht, pthread_attr_t **attr);

/*
 * cds_lfht_count_nodes - count the number of nodes in the hash table.
 *
 * Call with rcu_read_lock held.
 */
void cds_lfht_count_nodes(struct cds_lfht *ht,
		long *approx_before,
		unsigned long *count,
		unsigned long *removed,
		long *approx_after);

/*
 * cds_lfht_lookup - lookup a node by key.
 *
 * Output in "*iter". *iter->node set to NULL if not found.
 * Call with rcu_read_lock held.
 */
void cds_lfht_lookup(struct cds_lfht *ht, void *key, size_t key_len,
		struct cds_lfht_iter *iter);

/*
 * cds_lfht_next - get the next item with same key (after a lookup).
 *
 * Uses an iterator initialized by a lookup.
 * Sets *iter-node to the following node with same key.
 * Sets *iter->node to NULL if no following node exists with same key.
 * RCU read-side lock must be held across cds_lfht_lookup and
 * cds_lfht_next calls, and also between cds_lfht_next calls using the
 * node returned by a previous cds_lfht_next.
 * Call with rcu_read_lock held.
 */
void cds_lfht_next(struct cds_lfht *ht, struct cds_lfht_iter *iter);

/*
 * cds_lfht_add - add a node to the hash table.
 *
 * Call with rcu_read_lock held.
 * This function supports adding redundant keys into the table.
 */
void cds_lfht_add(struct cds_lfht *ht, struct cds_lfht_node *node);

/*
 * cds_lfht_add_unique - add a node to hash table, if key is not present.
 *
 * Return the node added upon success.
 * Return the unique node already present upon failure. If
 * cds_lfht_add_unique fails, the node passed as parameter should be
 * freed by the caller.
 * Call with rcu_read_lock held.
 *
 * The semantic of this function is that if only this function is used
 * to add keys into the table, no duplicated keys should ever be
 * observable in the table. The same guarantee apply for combination of
 * add_unique and add_replace (see below).
 */
struct cds_lfht_node *cds_lfht_add_unique(struct cds_lfht *ht,
		struct cds_lfht_node *node);

/*
 * cds_lfht_add_replace - replace or add a node within hash table.
 *
 * Return the node replaced upon success. If no node matching the key
 * was present, return NULL, which also means the operation succeeded.
 * This replacement operation should never fail.
 * Call with rcu_read_lock held.
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
		struct cds_lfht_node *node);

/*
 * cds_lfht_replace - replace a node pointer to by iter within hash table.
 *
 * Return 0 if replacement is successful, negative value otherwise.
 * Replacing a NULL old node or an already removed node will fail with a
 * negative value.
 * Old node can be looked up with cds_lfht_lookup and cds_lfht_next.
 * RCU read-side lock must be held between lookup and replacement.
 * Call with rcu_read_lock held.
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
 *
 * Return 0 if the node is successfully removed, negative value
 * otherwise.
 * Replacing a NULL node or an already removed node will fail with a
 * negative value.
 * Node can be looked up with cds_lfht_lookup and cds_lfht_next.
 * cds_lfht_iter_get_node.
 * RCU read-side lock must be held between lookup and removal.
 * Call with rcu_read_lock held.
 * After successful removal, a grace period must be waited for before
 * freeing the memory reserved for old node (which can be accessed with
 * cds_lfht_iter_get_node).
 */
int cds_lfht_del(struct cds_lfht *ht, struct cds_lfht_iter *iter);

/*
 * cds_lfht_resize - Force a hash table resize
 * @new_size: update to this hash table size.
 */
void cds_lfht_resize(struct cds_lfht *ht, unsigned long new_size);

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFHASH_H */
