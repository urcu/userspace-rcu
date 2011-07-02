
/*
 * TODO: keys are currently assumed <= sizeof(void *). Key target never freed.
 */

#define _LGPL_SOURCE
#include <stdlib.h>
#include <errno.h>
#include <assert.h>
#include <stdio.h>

#include <urcu.h>
#include <urcu-defer.h>
#include <urcu/arch.h>
#include <urcu/uatomic.h>
#include <urcu/jhash.h>
#include <urcu/compiler.h>
#include <stdio.h>
#include <pthread.h>
#include <urcu/rculfhash.h>

/*
 * Maximum number of hash table buckets: 256M on 64-bit.
 * Should take about 512MB max if we assume 1 node per 4 buckets.
 */
#define MAX_HT_BUCKETS ((256 << 10) / sizeof(void *))

/* node flags */
#define	NODE_STOLEN	(1 << 0)

struct rcu_ht_node;

struct rcu_ht_node {
	struct rcu_ht_node *next;
	void *key;
	void *data;
	unsigned int flags;
};

struct rcu_table {
	unsigned long size;
	struct rcu_ht_node *tbl[0];
};

struct rcu_ht {
	struct rcu_table *t;		/* shared */
	ht_hash_fct hash_fct;
	void (*free_fct)(void *data);	/* fct to free data */
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
	ht->keylen = keylen;
	ht->hashseed = hashseed;
	/* this mutex should not nest in read-side C.S. */
	pthread_mutex_init(&ht->resize_mutex, NULL);
	ht->resize_ongoing = 0;	/* shared */
	ht->t = calloc(1, sizeof(struct rcu_table)
		       + (init_size * sizeof(struct rcu_ht_node *)));
	ht->t->size = init_size;
	return ht;
}

void *ht_lookup(struct rcu_ht *ht, void *key)
{
	struct rcu_table *t;
	unsigned long hash;
	struct rcu_ht_node *node;
	void *ret;

	rcu_read_lock();
	t = rcu_dereference(ht->t);
	smp_read_barrier_depends();	/* read t before size and table */
	hash = ht->hash_fct(key, ht->keylen, ht->hashseed) % t->size;
	smp_read_barrier_depends();	/* read size before links */
	node = rcu_dereference(t->tbl[hash]);
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
	struct rcu_table *t;
	unsigned long hash;
	int ret = 0;

	new_head = calloc(1, sizeof(struct rcu_ht_node));
	new_head->key = key;
	new_head->data = data;
	new_head->flags = 0;
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

	if (unlikely(LOAD_SHARED(ht->resize_ongoing))) {
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

	t = rcu_dereference(ht->t);
	/* no read barrier needed, because no concurrency with resize */
	hash = ht->hash_fct(key, ht->keylen, ht->hashseed) % t->size;

	old_head = node = rcu_dereference(t->tbl[hash]);
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
	if (rcu_cmpxchg_pointer(&t->tbl[hash], old_head, new_head) != old_head)
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
 * Deal with concurrent stealers by doing an extra verification pass to check
 * that no element in the list are still pointing to the element stolen.
 * This could happen if two concurrent steal for consecutive objects are
 * executed. A pointer to an object being stolen could be saved by the
 * concurrent stealer for the previous object.
 * Also, given that in this precise scenario, another stealer can also want to
 * delete the doubly-referenced object; use a "stolen" flag to let only one
 * stealer delete the object.
 */
void *ht_steal(struct rcu_ht *ht, void *key)
{
	struct rcu_ht_node **prev, *node, *del_node = NULL;
	struct rcu_table *t;
	unsigned long hash;
	void *data;
	int ret;

retry:
	rcu_read_lock();

	if (unlikely(LOAD_SHARED(ht->resize_ongoing))) {
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

	t = rcu_dereference(ht->t);
	/* no read barrier needed, because no concurrency with resize */
	hash = ht->hash_fct(key, ht->keylen, ht->hashseed) % t->size;

	prev = &t->tbl[hash];
	node = rcu_dereference(*prev);
	for (;;) {
		if (likely(!node)) {
			if (del_node) {
				goto end;
			} else {
				goto error;
			}
		}
		if (node->key == key) {
			break;
		}
		prev = &node->next;
		node = rcu_dereference(*prev);
	}

	if (!del_node) {
		/*
		 * Another concurrent thread stole it ? If so, let it deal with
		 * this. Assume NODE_STOLEN is the only flag. If this changes,
		 * read flags before cmpxchg.
		 */
		if (cmpxchg(&node->flags, 0, NODE_STOLEN) != 0)
			goto error;
	}

	/* Found it ! pointer to object is in "prev" */
	if (rcu_cmpxchg_pointer(prev, node, node->next) == node)
		del_node = node;
	goto restart;

end:
	/*
	 * From that point, we own node. Note that there can still be concurrent
	 * RCU readers using it. We can free it outside of read lock after a GP.
	 */
	rcu_read_unlock();

	data = del_node->data;
	call_rcu(free, del_node);
	return data;

error:
	data = (void *)(unsigned long)-ENOENT;
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
	struct rcu_table *t;
	int cnt = 0;
	int ret;

	/*
	 * Mutual exclusion with resize operations, but leave add/steal execute
	 * concurrently. This is OK because we operate only on the heads.
	 */
	ret = pthread_mutex_lock(&ht->resize_mutex);
	assert(!ret);

	t = rcu_dereference(ht->t);
	/* no read barrier needed, because no concurrency with resize */
	for (i = 0; i < t->size; i++) {
		rcu_read_lock();
		prev = &t->tbl[i];
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
	free(ht->t);
	free(ht);
	return ret;
}

static void ht_resize_grow(struct rcu_ht *ht)
{
	unsigned long i, new_size, old_size;
	struct rcu_table *new_t, *old_t;
	struct rcu_ht_node *node, *new_node, *tmp;
	unsigned long hash;

	old_t = ht->t;
	old_size = old_t->size;

	if (old_size == MAX_HT_BUCKETS)
		return;

	new_size = old_size << 1;
	new_t = calloc(1, sizeof(struct rcu_table)
		       + (new_size * sizeof(struct rcu_ht_node *)));
	new_t->size = new_size;

	for (i = 0; i < old_size; i++) {
		/*
		 * Re-hash each entry, insert in new table.
		 * It's important that a reader looking for a key _will_ find it
		 * if it's in the table.
		 * Copy each node. (just the node, not ->data)
		 */
		node = old_t->tbl[i];
		while (node) {
			hash = ht->hash_fct(node->key, ht->keylen, ht->hashseed)
					    % new_size;
			new_node = malloc(sizeof(struct rcu_ht_node));
			new_node->key = node->key;
			new_node->data = node->data;
			new_node->flags = node->flags;
			new_node->next = new_t->tbl[hash]; /* link to first */
			new_t->tbl[hash] = new_node;	   /* add to head */
			node = node->next;
		}
	}

	/* Changing table and size atomically wrt lookups */
	rcu_assign_pointer(ht->t, new_t);

	/* Ensure all concurrent lookups use new size and table */
	synchronize_rcu();

	for (i = 0; i < old_size; i++) {
		node = old_t->tbl[i];
		while (node) {
			tmp = node->next;
			free(node);
			node = tmp;
		}
	}
	free(old_t);
}

static void ht_resize_shrink(struct rcu_ht *ht)
{
	unsigned long i, new_size;
	struct rcu_table *new_t, *old_t;
	struct rcu_ht_node **prev, *node;

	old_t = ht->t;
	if (old_t->size == 1)
		return;

	new_size = old_t->size >> 1;

	for (i = 0; i < new_size; i++) {
		/* Link end with first entry of i + new_size */
		prev = &old_t->tbl[i];
		node = *prev;
		while (node) {
			prev = &node->next;
			node = *prev;
		}
		*prev = old_t->tbl[i + new_size];
	}
	smp_wmb();	/* write links before changing size */
	STORE_SHARED(old_t->size, new_size);

	/* Ensure all concurrent lookups use new size */
	synchronize_rcu();

	new_t = realloc(old_t, sizeof(struct rcu_table)
			  + (new_size * sizeof(struct rcu_ht_node *)));
	/* shrinking, pointers should not move */
	assert(new_t == old_t);
}

/*
 * growth: >0: *2, <0: /2
 */
void ht_resize(struct rcu_ht *ht, int growth)
{
	int ret;

	ret = pthread_mutex_lock(&ht->resize_mutex);
	assert(!ret);
	STORE_SHARED(ht->resize_ongoing, 1);
	synchronize_rcu();
	/* All add/remove are waiting on the mutex. */
	if (growth > 0)
		ht_resize_grow(ht);
	else if (growth < 0)
		ht_resize_shrink(ht);
	smp_mb();
	STORE_SHARED(ht->resize_ongoing, 0);
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
