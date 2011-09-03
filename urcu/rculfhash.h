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
 * struct rcu_ht_node and struct _rcu_ht_node should be aligned on
 * 4-bytes boundaries because the two lower bits are used as flags.
 */

struct _rcu_ht_node {
	struct rcu_ht_node *next;	/* ptr | DUMMY_FLAG | REMOVED_FLAG */
	unsigned long reverse_hash;
};

struct rcu_ht_node {
	/* cache-hot for iteration */
	struct _rcu_ht_node p;          /* needs to be first field */
	void *key;
	unsigned int key_len;
	/* cache-cold for iteration */
	struct rcu_head head;
};

struct rcu_ht;

/*
 * Caution !
 * Ensure reader and writer threads are registered as urcu readers.
 */

typedef unsigned long (*ht_hash_fct)(void *key, size_t length,
				     unsigned long seed);
typedef unsigned long (*ht_compare_fct)(void *key1, size_t key1_len,
				        void *key2, size_t key2_len);

/*
 * ht_node_init - initialize a hash table node
 */
static inline
void ht_node_init(struct rcu_ht_node *node, void *key,
		  size_t key_len)
{
	node->key = key;
	node->key_len = key_len;
}

/*
 * ht_new - allocate a hash table.
 *
 * init_size must be power of two.
 */
struct rcu_ht *ht_new(ht_hash_fct hash_fct,
		      ht_compare_fct compare_fct,
		      unsigned long hash_seed,
		      unsigned long init_size,
		      void (*ht_call_rcu)(struct rcu_head *head,
				void (*func)(struct rcu_head *head)));

/*
 * ht_destroy - destroy a hash table.
 */
int ht_destroy(struct rcu_ht *ht);

/*
 * ht_count_nodes - count the number of nodes in the hash table.
 *
 * Call with rcu_read_lock held.
 */
void ht_count_nodes(struct rcu_ht *ht,
		unsigned long *count,
		unsigned long *removed);

/*
 * ht_lookup - lookup a node by key.
 *
 * Returns NULL if not found.
 * Call with rcu_read_lock held.
 */
struct rcu_ht_node *ht_lookup(struct rcu_ht *ht, void *key, size_t key_len);

/*
 * ht_next - get the next item with same key (after a lookup).
 *
 * Returns NULL if no following node exists with same key.
 * RCU read-side lock must be held across ht_lookup and ht_next calls, and also
 * between ht_next calls using the node returned by a previous ht_next.
 * Call with rcu_read_lock held.
 */
struct rcu_ht_node *ht_next(struct rcu_ht *ht, struct rcu_ht_node *node);

/*
 * ht_add - add a node to the hash table.
 *
 * Call with rcu_read_lock held.
 */
void ht_add(struct rcu_ht *ht, struct rcu_ht_node *node);

/*
 * ht_add_unique - add a node to hash table, if key is not present.
 *
 * Returns the node added upon success.
 * Returns the unique node already present upon failure. If ht_add_unique fails,
 * the node passed as parameter should be freed by the caller.
 * Call with rcu_read_lock held.
 */
struct rcu_ht_node *ht_add_unique(struct rcu_ht *ht, struct rcu_ht_node *node);

/*
 * ht_remove - remove node from hash table.
 *
 * Node can be looked up with ht_lookup. RCU read-side lock must be held between
 * lookup and removal.
 * Call with rcu_read_lock held.
 */
int ht_remove(struct rcu_ht *ht, struct rcu_ht_node *node);

/*
 * ht_resize - Force a hash table resize
 * @growth: growth order (current size is multiplied by 2^growth)
 *
 * Currently, only expand operation is supported (growth >= 0).
 */
void ht_resize(struct rcu_ht *ht, int growth);

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFHASH_H */
