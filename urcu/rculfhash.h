#ifndef _URCU_RCULFHASH_H
#define _URCU_RCULFHASH_H

#include <stdint.h>
#include <urcu-call-rcu.h>

#ifdef __cplusplus
extern "C" {
#endif

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

static inline
void ht_node_init(struct rcu_ht_node *node, void *key,
		  size_t key_len)
{
	node->key = key;
	node->key_len = key_len;
}

/*
 * init_size must be power of two.
 */
struct rcu_ht *ht_new(ht_hash_fct hash_fct,
		      ht_compare_fct compare_fct,
		      unsigned long hash_seed,
		      unsigned long init_size,
		      void (*ht_call_rcu)(struct rcu_head *head,
				void (*func)(struct rcu_head *head)));

int ht_destroy(struct rcu_ht *ht);
/* Count the number of nodes in the hash table. Call with rcu_read_lock held. */
void ht_count_nodes(struct rcu_ht *ht,
		unsigned long *count,
		unsigned long *removed);

/* Call with rcu_read_lock held. */
struct rcu_ht_node *ht_lookup(struct rcu_ht *ht, void *key, size_t key_len);

/* Call with rcu_read_lock held. */
void ht_add(struct rcu_ht *ht, struct rcu_ht_node *node);

/*
 * Call with rcu_read_lock held.
 * Returns the node added upon success.
 * Returns the unique node already present upon failure. If ht_add_unique fails,
 * the node passed as parameter should be freed by the caller.
 */
struct rcu_ht_node *ht_add_unique(struct rcu_ht *ht, struct rcu_ht_node *node);

/* Call with rcu_read_lock held. */
int ht_remove(struct rcu_ht *ht, struct rcu_ht_node *node);

void ht_resize(struct rcu_ht *ht, int growth);

#ifdef __cplusplus
}
#endif

#endif /* _URCU_RCULFHASH_H */
