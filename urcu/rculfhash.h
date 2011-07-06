#ifndef _URCU_RCULFHASH_H
#define _URCU_RCULFHASH_H

#include <stdint.h>
#include <urcu-call-rcu.h>

struct rcu_ht_node {
	struct rcu_ht_node *next;
	void *key;
	unsigned long hash;
	unsigned long reverse_hash;
	unsigned int dummy;
	void *value;
	struct rcu_head head;
};

struct rcu_ht;

/*
 * Caution !
 * Ensure reader and writer threads are registered as urcu readers.
 */

typedef unsigned long (*ht_hash_fct)(void *hashseed, void *key);

static inline
void ht_node_init(struct rcu_ht_node *node, void *key, void *value)
{
	node->key = key;
	node->value = value;
	node->dummy = 0;
}

/*
 * init_size must be power of two.
 */
struct rcu_ht *ht_new(ht_hash_fct hash_fct,
		      void *hashseed,
		      unsigned long init_size,
		      void (*ht_call_rcu)(struct rcu_head *head,
				void (*func)(struct rcu_head *head)));

int ht_destroy(struct rcu_ht *ht);

/* Call with rcu_read_lock held. */
struct rcu_ht_node *ht_lookup(struct rcu_ht *ht, void *key);

/* Call with rcu_read_lock held. */
void ht_add(struct rcu_ht *ht, struct rcu_ht_node *node);

/* Call with rcu_read_lock held. */
int ht_remove(struct rcu_ht *ht, struct rcu_ht_node *node);

void ht_resize(struct rcu_ht *ht, int growth);

#endif /* _URCU_RCULFHASH_H */
