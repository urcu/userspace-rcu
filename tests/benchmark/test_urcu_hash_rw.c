/*
 * test_urcu_hash_rw.c
 *
 * Userspace RCU library - test program
 *
 * Copyright 2009-2012 - Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

#include "test_urcu_hash.h"

enum urcu_hash_addremove {
	AR_RANDOM = 0,
	AR_ADD = 1,
	AR_REMOVE = -1,
};	/* 1: add, -1 remove, 0: random */

static enum urcu_hash_addremove addremove; /* 1: add, -1 remove, 0: random */

void test_hash_rw_sigusr1_handler(int signo)
{
	switch (addremove) {
	case AR_ADD:
		printf("Add/Remove: random.\n");
		addremove = AR_RANDOM;
		break;
	case AR_RANDOM:
		printf("Add/Remove: remove only.\n");
		addremove = AR_REMOVE;
		break;
	case AR_REMOVE:
		printf("Add/Remove: add only.\n");
		addremove = AR_ADD;
		break;
	}
}

void test_hash_rw_sigusr2_handler(int signo)
{
	char msg[1] = { 0x42 };
	ssize_t ret;

	do {
		ret = write(count_pipe[1], msg, 1);	/* wakeup thread */
	} while (ret == -1L && errno == EINTR);
}

void *test_hash_rw_thr_reader(void *_count)
{
	unsigned long long *count = _count;
	struct lfht_test_node *node;
	struct cds_lfht_iter iter;

	printf_verbose("thread_begin %s, tid %lu\n",
			"reader", urcu_get_thread_id());

	URCU_TLS(rand_lookup) = urcu_get_thread_id() ^ time(NULL);

	set_affinity();

	rcu_register_thread();

	while (!test_go)
	{
	}
	cmm_smp_mb();

	for (;;) {
		rcu_read_lock();
		cds_lfht_test_lookup(test_ht,
			(void *)(((unsigned long) rand_r(&URCU_TLS(rand_lookup)) % lookup_pool_size) + lookup_pool_offset),
			sizeof(void *), &iter);
		node = cds_lfht_iter_get_test_node(&iter);
		if (node == NULL) {
			if (validate_lookup) {
				printf("[ERROR] Lookup cannot find initial node.\n");
				exit(-1);
			}
			URCU_TLS(lookup_fail)++;
		} else {
			URCU_TLS(lookup_ok)++;
		}
		rcu_debug_yield_read();
		if (caa_unlikely(rduration))
			loop_sleep(rduration);
		rcu_read_unlock();
		URCU_TLS(nr_reads)++;
		if (caa_unlikely(!test_duration_read()))
			break;
		if (caa_unlikely((URCU_TLS(nr_reads) & ((1 << 10) - 1)) == 0))
			rcu_quiescent_state();
	}

	rcu_unregister_thread();

	*count = URCU_TLS(nr_reads);
	printf_verbose("thread_end %s, tid %lu\n",
			"reader", urcu_get_thread_id());
	printf_verbose("read tid : %lx, lookupfail %lu, lookupok %lu\n",
			urcu_get_thread_id(),
			URCU_TLS(lookup_fail),
			URCU_TLS(lookup_ok));
	return ((void*)1);

}

void *test_hash_rw_thr_writer(void *_count)
{
	struct lfht_test_node *node;
	struct cds_lfht_iter iter;
	struct wr_count *count = _count;
	int ret;

	printf_verbose("thread_begin %s, tid %lu\n",
			"writer", urcu_get_thread_id());

	URCU_TLS(rand_lookup) = urcu_get_thread_id() ^ time(NULL);

	set_affinity();

	rcu_register_thread();

	while (!test_go)
	{
	}
	cmm_smp_mb();

	for (;;) {
		struct cds_lfht_node *ret_node = NULL;

		if ((addremove == AR_ADD || add_only)
				|| (addremove == AR_RANDOM && rand_r(&URCU_TLS(rand_lookup)) & 1)) {
			node = malloc(sizeof(struct lfht_test_node));
			lfht_test_node_init(node,
				(void *)(((unsigned long) rand_r(&URCU_TLS(rand_lookup)) % write_pool_size) + write_pool_offset),
				sizeof(void *));
			rcu_read_lock();
			if (add_unique) {
				ret_node = cds_lfht_add_unique(test_ht,
					test_hash(node->key, node->key_len, TEST_HASH_SEED),
					test_match, node->key, &node->node);
			} else {
				if (add_replace)
					ret_node = cds_lfht_add_replace(test_ht,
							test_hash(node->key, node->key_len, TEST_HASH_SEED),
							test_match, node->key, &node->node);
				else
					cds_lfht_add(test_ht,
						test_hash(node->key, node->key_len, TEST_HASH_SEED),
						&node->node);
			}
			rcu_read_unlock();
			if (add_unique && ret_node != &node->node) {
				free(node);
				URCU_TLS(nr_addexist)++;
			} else {
				if (add_replace && ret_node) {
					call_rcu(&to_test_node(ret_node)->head,
							free_node_cb);
					URCU_TLS(nr_addexist)++;
				} else {
					URCU_TLS(nr_add)++;
				}
			}
		} else {
			/* May delete */
			rcu_read_lock();
			cds_lfht_test_lookup(test_ht,
				(void *)(((unsigned long) rand_r(&URCU_TLS(rand_lookup)) % write_pool_size) + write_pool_offset),
				sizeof(void *), &iter);
			ret = cds_lfht_del(test_ht, cds_lfht_iter_get_node(&iter));
			rcu_read_unlock();
			if (ret == 0) {
				node = cds_lfht_iter_get_test_node(&iter);
				call_rcu(&node->head, free_node_cb);
				URCU_TLS(nr_del)++;
			} else
				URCU_TLS(nr_delnoent)++;
		}
#if 0
		//if (URCU_TLS(nr_writes) % 100000 == 0) {
		if (URCU_TLS(nr_writes) % 1000 == 0) {
			rcu_read_lock();
			if (rand_r(&URCU_TLS(rand_lookup)) & 1) {
				ht_resize(test_ht, 1);
			} else {
				ht_resize(test_ht, -1);
			}
			rcu_read_unlock();
		}
#endif //0
		URCU_TLS(nr_writes)++;
		if (caa_unlikely(!test_duration_write()))
			break;
		if (caa_unlikely(wdelay))
			loop_sleep(wdelay);
		if (caa_unlikely((URCU_TLS(nr_writes) & ((1 << 10) - 1)) == 0))
			rcu_quiescent_state();
	}

	rcu_unregister_thread();

	printf_verbose("thread_end %s, tid %lu\n",
			"writer", urcu_get_thread_id());
	printf_verbose("info tid %lu: nr_add %lu, nr_addexist %lu, nr_del %lu, "
			"nr_delnoent %lu\n", urcu_get_thread_id(),
			URCU_TLS(nr_add),
			URCU_TLS(nr_addexist),
			URCU_TLS(nr_del),
			URCU_TLS(nr_delnoent));
	count->update_ops = URCU_TLS(nr_writes);
	count->add = URCU_TLS(nr_add);
	count->add_exist = URCU_TLS(nr_addexist);
	count->remove = URCU_TLS(nr_del);
	return ((void*)2);
}

int test_hash_rw_populate_hash(void)
{
	struct lfht_test_node *node;

	if (!init_populate)
		return 0;

	printf("Starting rw test\n");

	URCU_TLS(rand_lookup) = urcu_get_thread_id() ^ time(NULL);

	if ((add_unique || add_replace) && init_populate * 10 > init_pool_size) {
		printf("WARNING: required to populate %lu nodes (-k), but random "
"pool is quite small (%lu values) and we are in add_unique (-u) or add_replace (-s) mode. Try with a "
"larger random pool (-p option). This may take a while...\n", init_populate, init_pool_size);
	}

	while (URCU_TLS(nr_add) < init_populate) {
		struct cds_lfht_node *ret_node = NULL;

		node = malloc(sizeof(struct lfht_test_node));
		lfht_test_node_init(node,
			(void *)(((unsigned long) rand_r(&URCU_TLS(rand_lookup)) % init_pool_size) + init_pool_offset),
			sizeof(void *));
		rcu_read_lock();
		if (add_unique) {
			ret_node = cds_lfht_add_unique(test_ht,
				test_hash(node->key, node->key_len, TEST_HASH_SEED),
				test_match, node->key, &node->node);
		} else {
			if (add_replace)
				ret_node = cds_lfht_add_replace(test_ht,
						test_hash(node->key, node->key_len, TEST_HASH_SEED),
						test_match, node->key, &node->node);
			else
				cds_lfht_add(test_ht,
					test_hash(node->key, node->key_len, TEST_HASH_SEED),
					&node->node);
		}
		rcu_read_unlock();
		if (add_unique && ret_node != &node->node) {
			free(node);
			URCU_TLS(nr_addexist)++;
		} else {
			if (add_replace && ret_node) {
				call_rcu(&to_test_node(ret_node)->head, free_node_cb);
				URCU_TLS(nr_addexist)++;
			} else {
				URCU_TLS(nr_add)++;
			}
		}
		URCU_TLS(nr_writes)++;
	}
	return 0;
}
