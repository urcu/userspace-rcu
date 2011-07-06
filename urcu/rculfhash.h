#ifndef _URCU_RCULFHASH_H
#define _URCU_RCULFHASH_H

#include <stdint.h>
#include <urcu-call-rcu.h>

struct rcu_ht_node {
	struct rcu_ht_node *next;
	void *key;
	size_t key_len;
	unsigned long hash;
	unsigned long reverse_hash;
	unsigned int dummy;
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
	node->dummy = 0;
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

/* Call with rcu_read_lock held. */
struct rcu_ht_node *ht_lookup(struct rcu_ht *ht, void *key, size_t key_len);

/* Call with rcu_read_lock held. */
void ht_add(struct rcu_ht *ht, struct rcu_ht_node *node);

/* Call with rcu_read_lock held. */
int ht_add_unique(struct rcu_ht *ht, struct rcu_ht_node *node);

/* Call with rcu_read_lock held. */
int ht_remove(struct rcu_ht *ht, struct rcu_ht_node *node);

void ht_resize(struct rcu_ht *ht, int growth);

#endif /* _URCU_RCULFHASH_H */
