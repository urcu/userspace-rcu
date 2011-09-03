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
};

struct cds_lfht_node {
	/* cache-hot for iteration */
	struct _cds_lfht_node p;          /* needs to be first field */
	void *key;
	unsigned int key_len;
	/* cache-cold for iteration */
	struct rcu_head head;
};

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
 * cds_lfht_new - allocate a hash table.
 *
 * init_size must be power of two.
 * Return NULL on error.
 */
struct cds_lfht *cds_lfht_new(cds_lfht_hash_fct hash_fct,
			cds_lfht_compare_fct compare_fct,
			unsigned long hash_seed,
			unsigned long init_size,
			void (*cds_lfht_call_rcu)(struct rcu_head *head,
				void (*func)(struct rcu_head *head)));

/*
 * cds_lfht_destroy - destroy a hash table.
 *
 * Return 0 on success, negative error value on error.
 */
int cds_lfht_destroy(struct cds_lfht *ht);

/*
 * cds_lfht_count_nodes - count the number of nodes in the hash table.
 *
 * Call with rcu_read_lock held.
 */
void cds_lfht_count_nodes(struct cds_lfht *ht,
			unsigned long *count,
			unsigned long *removed);

/*
 * cds_lfht_lookup - lookup a node by key.
 *
 * Return NULL if not found.
 * Call with rcu_read_lock held.
 */
struct cds_lfht_node *cds_lfht_lookup(struct cds_lfht *ht, void *key, size_t key_len);

/*
 * cds_lfht_next - get the next item with same key (after a lookup).
 *
 * Return NULL if no following node exists with same key.
 * RCU read-side lock must be held across cds_lfht_lookup and cds_lfht_next calls, and also
 * between cds_lfht_next calls using the node returned by a previous cds_lfht_next.
 * Call with rcu_read_lock held.
 */
struct cds_lfht_node *cds_lfht_next(struct cds_lfht *ht, struct cds_lfht_node *node);

/*
 * cds_lfht_add - add a node to the hash table.
 *
 * Call with rcu_read_lock held.
 */
void cds_lfht_add(struct cds_lfht *ht, struct cds_lfht_node *node);

/*
 * cds_lfht_add_unique - add a node to hash table, if key is not present.
 *
 * Return the node added upon success.
 * Return the unique node already present upon failure. If cds_lfht_add_unique fails,
 * the node passed as parameter should be freed by the caller.
 * Call with rcu_read_lock held.
 */
struct cds_lfht_node *cds_lfht_add_unique(struct cds_lfht *ht, struct cds_lfht_node *node);

/*
 * cds_lfht_remove - remove node from hash table.
 *
 * Node can be looked up with cds_lfht_lookup. RCU read-side lock must be held between
 * lookup and removal.
 * Call with rcu_read_lock held.
 */
int cds_lfht_remove(struct cds_lfht *ht, struct cds_lfht_node *node);

/*
 * cds_lfht_resize - Force a hash table resize
 * @growth: growth order (current size is multiplied by 2^growth)
 *
 * Currently, only expand operation is supported (growth >= 0).
 */
void cds_lfht_resize(struct cds_lfht *ht, int growth);

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFHASH_H */
