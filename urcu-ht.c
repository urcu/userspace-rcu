
/*
 * TODO: keys are currently assumed <= sizeof(void *). Key target never freed.
 */

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
#include <urcu/jhash.h>
#include <stdio.h>
#include <pthread.h>

struct rcu_ht_node;

struct rcu_ht_node {
	struct rcu_ht_node *next;
	void *key;
	void *data;
};

struct rcu_ht {
	struct rcu_ht_node **tbl;
	ht_hash_fct hash_fct;
	void (*free_fct)(void *data);	/* fct to free data */
	unsigned long size;
	uint32_t keylen;
	uint32_t hashseed;
	pthread_mutex_t resize_mutex;	/* resize mutex: add/del mutex */
	int resize_ongoing;		/* fast-path resize check */
};

struct rcu_ht *ht_new(ht_hash_fct hash_fct, void (*free_fct)(void *data),
		      unsigned long init_size, uint32_t keylen,
		      uint32_t hashseed)
{
	struct rcu_ht *ht;

	ht = calloc(1, sizeof(struct rcu_ht));
	ht->hash_fct = hash_fct;
	ht->free_fct = free_fct;
	ht->size = init_size;
	ht->keylen = keylen;
	ht->hashseed = hashseed;
	/* this mutex should not nest in read-side C.S. */
	pthread_mutex_init(&ht->resize_mutex, NULL);
	ht->resize_ongoing = 0;
	ht->tbl = calloc(init_size, sizeof(struct rcu_ht_node *));
	return ht;
}

void *ht_lookup(struct rcu_ht *ht, void *key)
{
	unsigned long hash;
	struct rcu_ht_node *node;
	void *ret;

	hash = ht->hash_fct(key, ht->keylen, ht->hashseed) % ht->size;
	smp_read_barrier_depends();	/* read size before links */

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

	if (unlikely(ht->resize_ongoing)) {
		rcu_read_unlock();
		/*
		 * Wait for resize to complete before continuing.
		 */
		ret = pthread_mutex_lock(&ht->resize_mutex);
		assert(!ret);
		ret = pthread_mutex_unlock(&ht->resize_mutex);
		assert(!ret);
		goto retry;
	}

	hash = ht->hash_fct(key, ht->keylen, ht->hashseed) % ht->size;

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
	new_head->next = old_head;
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
 * Deal with concurrent stealers by verifying that there are no element
 * in the list still pointing to the element stolen. (del_node)
 */
void *ht_steal(struct rcu_ht *ht, void *key)
{
	struct rcu_ht_node **prev, *node, *del_node = NULL;
	unsigned long hash;
	void *data;
	int ret;

retry:
	rcu_read_lock();

	if (unlikely(ht->resize_ongoing)) {
		rcu_read_unlock();
		/*
		 * Wait for resize to complete before continuing.
		 */
		ret = pthread_mutex_lock(&ht->resize_mutex);
		assert(!ret);
		ret = pthread_mutex_unlock(&ht->resize_mutex);
		assert(!ret);
		goto retry;
	}

	hash = ht->hash_fct(key, ht->keylen, ht->hashseed) % ht->size;

	prev = &ht->tbl[hash];
	node = rcu_dereference(*prev);
	for (;;) {
		if (likely(!node)) {
			if (del_node) {
				goto end;
			} else {
				data = (void *)(unsigned long)-ENOENT;
				goto error;
			}
		}
		if (node->key == key) {
			break;
		}
		prev = &node->next;
		node = rcu_dereference(*prev);
	}
	/* Found it ! pointer to object is in "prev" */
	if (rcu_cmpxchg_pointer(prev, node, node->next) != node)
		del_node = node;
	goto restart;

end:
	/*
	 * From that point, we own node. Note that there can still be concurrent
	 * RCU readers using it. We can free it outside of read lock after a GP.
	 */
	rcu_read_unlock();

	data = node->data;
	call_rcu(free, node);
	return data;

error:
	rcu_read_unlock();
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
	if (data && data != (void *)(unsigned long)-ENOENT) {
		if (ht->free_fct)
			call_rcu(ht->free_fct, data);
		return 0;
	} else {
		return -ENOENT;
	}
}

/* Delete all old elements. Allow concurrent writer accesses. */
int ht_delete_all(struct rcu_ht *ht)
{
	unsigned long i;
	struct rcu_ht_node **prev, *node, *inext;
	int cnt = 0;
	int ret;

	/*
	 * Mutual exclusion with resize operations, but leave add/steal execute
	 * concurrently. This is OK because we operate only on the heads.
	 */
	ret = pthread_mutex_lock(&ht->resize_mutex);
	assert(!ret);

	for (i = 0; i < ht->size; i++) {
		rcu_read_lock();
		prev = &ht->tbl[i];
		/*
		 * Cut the head. After that, we own the first element.
		 */
		node = rcu_xchg_pointer(prev, NULL);
		if (!node) {
			rcu_read_unlock();
			continue;
		}
		/*
		 * We manage a list shared with concurrent writers and readers.
		 * Note that a concurrent add may or may not be deleted by us,
		 * depending if it arrives before or after the head is cut.
		 * "node" points to our first node. Remove first elements
		 * iteratively.
		 */
		for (;;) {
			inext = NULL;
			prev = &node->next;
			if (prev)
				inext = rcu_xchg_pointer(prev, NULL);
			/*
			 * "node" is the first element of the list we have cut.
			 * We therefore own it, no concurrent writer may delete
			 * it. There can only be concurrent lookups. Concurrent
			 * add can only be done on a bucket head, but we've cut
			 * it already. inext is also owned by us, because we
			 * have exchanged it for "NULL". It will therefore be
			 * safe to use it after a G.P.
			 */
			rcu_read_unlock();
			if (node->data)
				call_rcu(ht->free_fct, node->data);
			call_rcu(free, node);
			cnt++;
			if (likely(!inext))
				break;
			rcu_read_lock();
			node = inext;
		}
	}

	ret = pthread_mutex_unlock(&ht->resize_mutex);
	assert(!ret);
	return cnt;
}

/*
 * Should only be called when no more concurrent readers nor writers can
 * possibly access the table.
 */
int ht_destroy(struct rcu_ht *ht)
{
	int ret;

	ret = ht_delete_all(ht);
	free(ht->tbl);
	free(ht);
	return ret;
}

static void ht_resize_grow(struct rcu_ht *ht)
{
	unsigned long i, new_size, old_size;
	struct rcu_ht_node **new_tbl, **old_tbl;
	struct rcu_ht_node *node, *new_node, *tmp;
	unsigned long hash;

	old_size = ht->size;

	if (old_size == 1)
		return;

	new_size = old_size << 1;
	new_tbl = calloc(new_size, sizeof(struct rcu_ht_node *));

	for (i = 0; i < old_size; i++) {
		/*
		 * Re-hash each entry, insert in new table.
		 * It's important that a reader looking for a key _will_ find it
		 * if it's in the table.
		 * Copy each node. (just the node, not ->data)
		 */
		node = ht->tbl[i];
		while (node) {
			hash = ht->hash_fct(node->key, ht->keylen, ht->hashseed)
					    % new_size;
			new_node = malloc(sizeof(struct rcu_ht_node));
			new_node->key = node->key;
			new_node->data = node->data;
			new_node->next = new_tbl[i];	/* add to head */
			new_tbl[i] = new_node;
			node = node->next;
		}
	}

	old_tbl = ht->tbl;
	ht->tbl = new_tbl;
	smp_wmb();	/* write links and table before changing size */
	ht->size = new_size;

	/* Ensure all concurrent lookups use new size and table */
	synchronize_rcu();

	for (i = 0; i < old_size; i++) {
		node = old_tbl[i];
		while (node) {
			tmp = node->next;
			free(node);
			node = tmp;
		}
	}
	free(old_tbl);
}

static void ht_resize_shrink(struct rcu_ht *ht)
{
	unsigned long i, new_size;
	struct rcu_ht_node **new_tbl;
	struct rcu_ht_node **prev, *node;

	if (ht->size == 1)
		return;

	new_size = ht->size >> 1;

	for (i = 0; i < new_size; i++) {
		/* Link end with first entry of 2*i */
		prev = &ht->tbl[i];
		node = *prev;
		while (node) {
			prev = &node->next;
			node = *prev;
		}
		*prev = ht->tbl[i << 1];
	}
	smp_wmb();	/* write links before changing size */
	ht->size = new_size;

	/* Ensure all concurrent lookups use new size */
	synchronize_rcu();

	new_tbl = realloc(ht->tbl, new_size * sizeof(struct rcu_ht_node *));
	/* shrinking, pointers should not move */
	assert(new_tbl == ht->tbl);
}

/*
 * growth: >0: *2, <0: /2
 */
void ht_resize(struct rcu_ht *ht, int growth)
{
	int ret;

	ret = pthread_mutex_lock(&ht->resize_mutex);
	assert(!ret);
	ht->resize_ongoing = 1;
	synchronize_rcu();
	/* All add/remove are waiting on the mutex. */
	if (growth > 0)
		ht_resize_grow(ht);
	else if (growth < 0)
		ht_resize_shrink(ht);
	smp_mb();
	ht->resize_ongoing = 0;
	ret = pthread_mutex_unlock(&ht->resize_mutex);
	assert(!ret);
}

/*
 * Expects keys <= than pointer size to be encoded in the pointer itself.
 */
uint32_t ht_jhash(void *key, uint32_t length, uint32_t initval)
{
	uint32_t ret;
	void *vkey;

	if (length <= sizeof(void *))
		vkey = &key;
	else
		vkey = key;
	ret = jhash(vkey, length, initval);
	return ret;
}
