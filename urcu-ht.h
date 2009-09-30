#ifndef _URCU_HT_H
#define _URCU_HT_H

#include <stdint.h>

typedef uint32_t (*ht_hash_fct)(void *key);

/*
 * init_size must be power of two.
 */
struct rcu_ht *ht_new(ht_hash_fct hash_fct, void (*free_fct)(void *data),
		      unsigned long init_size);

void ht_delete_all(struct rcu_ht *ht);

void ht_destroy(struct rcu_ht *ht);

void *ht_lookup(struct rcu_ht *ht, void *key);

int ht_add(struct rcu_ht *ht, void *key, void *data);

int ht_delete(struct rcu_ht *ht, void *key);

void *ht_steal(struct rcu_ht *ht, void *key);

uint32_t ht_jhash(void *key, u32 length, u32 initval);

#endif /* _URCU_HT_H */
