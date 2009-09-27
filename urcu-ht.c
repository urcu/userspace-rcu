
#define _LGPL_SOURCE
#include <stdlib.h>
#include <urcu.h>
#include <arch.h>
#include <arch_atomic.h>
#include <assert.h>
#include <compiler.h>
#include <urcu-defer.h>
#include <errno.h>
#include <urcu-ht.h>

struct rcu_ht_node;

struct rcu_ht_node {
	struct rcu_ht_node *next;
	void *key;
	void *data;
};

struct rcu_ht {
	struct rcu_ht_node *tbl[HASH_SIZE];
	ht_hash_fct hash_fct;
	void (*free_fct)(void *data);	/* fct to free data */
};

struct rcu_ht *ht_new(ht_hash_fct hash_fct, void (*free_fct)(void *data))
{
	struct rcu_ht *ht;

	ht = calloc(1, sizeof(struct rcu_ht));
	ht->hash_fct = hash_fct;
	ht->free_fct = free_fct;
	return ht;
}

/* delete all elements */
void ht_delete_all(struct rcu_ht *ht)
{
	unsigned long i;
	struct rcu_ht_node **prev, *node;

	for (i = 0; i < HASH_SIZE; i++) {
		rcu_read_lock();

		prev = &ht->tbl[i];
		node = rcu_dereference(*prev);
		/*
		 * Cut the head, therefore whole bucket will be unused
		 * after GP. (except for concurrent additions)
		 */
		rcu_assign_pointer(prev, NULL);
		for (;;) {
			if (likely(!node)) {
				break;
			}
			prev = &node->next;
			/*
			 * FIXME: calling call_rcu within a read-side C.S. is a
			 * bug, because it may call synchronize_rcu() if the
			 * callback queue is full.
			 */
			if (node->data)
				call_rcu(ht->free_fct, node->data);
			call_rcu(free, node);
			node = rcu_dereference(*prev);
		}
		rcu_read_unlock();
	}
}

/*
 * Should only be called when no more concurrent readers nor writers can
 * possibly access the table.
 */
void ht_destroy(struct rcu_ht *ht)
{
	ht_delete_all(ht);
	free(ht);
}

void *ht_lookup(struct rcu_ht *ht, void *key)
{
	unsigned long hash;
	struct rcu_ht_node *node;
	void *ret;

	hash = ht->hash_fct(key);

	rcu_read_lock();
	node = rcu_dereference(ht->tbl[hash]);
	for (;;) {
		if (likely(!node)) {
			ret = NULL;
			break;
		}
		if (node->key == key) {
			ret = node->data;
			break;
		}
		node = rcu_dereference(node->next);
	}
	rcu_read_unlock();

	return ret;
}

/*
 * Will re-try until either:
 * - The key is already there (-EEXIST)
 * - We successfully add the key at the head of a table bucket.
 */
int ht_add(struct rcu_ht *ht, void *key, void *data)
{
	struct rcu_ht_node *node, *old_head, *new_head;
	unsigned long hash;
	int ret = 0;

	new_head = calloc(1, sizeof(struct rcu_ht_node));
	new_head->key = key;
	new_head->data = data;
	hash = ht->hash_fct(key);

	/* here comes the fun and tricky part.
	 * Add at the beginning with a cmpxchg.
	 * Hold a read lock between the moment the first element is read
	 * and the nodes traversal (to find duplicates). This ensures
	 * the head pointer has not been reclaimed when cmpxchg is done.
	 * Always adding at the head ensures that we would have to
	 * re-try if a new item has been added concurrently. So we ensure that
	 * we never add duplicates. */
retry:
	rcu_read_lock();

	old_head = node = rcu_dereference(ht->tbl[hash]);
	for (;;) {
		if (likely(!node)) {
			break;
		}
		if (node->key == key) {
			ret = -EEXIST;
			goto end;
		}
		node = rcu_dereference(node->next);
	}
	if (rcu_cmpxchg_pointer(&ht->tbl[hash], old_head, new_head) != old_head)
		goto restart;
end:
	rcu_read_unlock();

	return ret;

	/* restart loop, release and re-take the read lock to be kind to GP */
restart:
	rcu_read_unlock();
	goto retry;
}

/*
 * Restart until we successfully remove the entry, or no entry is left
 * ((void *)(unsigned long)-ENOENT).
 */
void *ht_steal(struct rcu_ht *ht, void *key)
{
	struct rcu_ht_node **prev, *node;
	unsigned long hash;
	void *data;

	hash = ht->hash_fct(key);

retry:
	rcu_read_lock();

	prev = &ht->tbl[hash];
	node = rcu_dereference(*prev);
	for (;;) {
		if (likely(!node)) {
			data = (void *)(unsigned long)-ENOENT;
			goto end;
		}
		if (node->key == key) {
			break;
		}
		prev = &node->next;
		node = rcu_dereference(*prev);
	}
	/* Found it ! pointer to object is in "prev" */
	if (rcu_cmpxchg_pointer(prev, node, node->next) != node)
		goto restart;
end:
	rcu_read_unlock();

	data = node->data;
	call_rcu(free, node);

	return data;

	/* restart loop, release and re-take the read lock to be kind to GP */
restart:
	rcu_read_unlock();
	goto retry;
}

int ht_delete(struct rcu_ht *ht, void *key)
{
	void *data;

	data = ht_steal(ht, key);
	if (data) {
		if (ht->free_fct && data)
			call_rcu(ht->free_fct, data);
		return 0;
	} else {
		return -ENOENT;
	}
}

unsigned long stupid_hash(void *key)
{
	return (unsigned long)key % HASH_SIZE;
}
