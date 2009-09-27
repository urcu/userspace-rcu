#ifndef _URCU_HT_H
#define _URCU_HT_H

#define HASH_SIZE	4096
typedef unsigned long (*ht_hash_fct)(void *key);

struct rcu_ht *ht_new(ht_hash_fct hash_fct, void (*free_fct)(void *data));

void ht_delete_all(struct rcu_ht *ht);

void ht_destroy(struct rcu_ht *ht);

void *ht_lookup(struct rcu_ht *ht, void *key);

int ht_add(struct rcu_ht *ht, void *key, void *data);

int ht_delete(struct rcu_ht *ht, void *key);

void *ht_steal(struct rcu_ht *ht, void *key);

unsigned long stupid_hash(void *key);

#endif /* _URCU_HT_H */
