#ifndef _URCU_HT_H
#define _URCU_HT_H

#include <stdint.h>

/*
 * Caution !
 * Ensure writer threads are registered as urcu readers and with with
 * urcu-defer.
 * Ensure reader threads are registered as urcu readers.
 */

typedef uint32_t (*ht_hash_fct)(void *key, uint32_t length, uint32_t initval);

/*
 * init_size must be power of two.
 */
struct rcu_ht *ht_new(ht_hash_fct hash_fct, void (*free_fct)(void *data),
		      unsigned long init_size, uint32_t keylen,
		      uint32_t hashseed);

int ht_delete_all(struct rcu_ht *ht);

int ht_destroy(struct rcu_ht *ht);

void *ht_lookup(struct rcu_ht *ht, void *key);

int ht_add(struct rcu_ht *ht, void *key, void *data);

int ht_delete(struct rcu_ht *ht, void *key);

void *ht_steal(struct rcu_ht *ht, void *key);

uint32_t ht_jhash(void *key, uint32_t length, uint32_t initval);

#endif /* _URCU_HT_H */
