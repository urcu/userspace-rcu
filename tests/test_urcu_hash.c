/*
 * test_urcu_hash.c
 *
 * Userspace RCU library - test program
 *
 * Copyright February 2009 - Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
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

#define _GNU_SOURCE
#include <stdio.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <sched.h>
#include <errno.h>

#ifdef __linux__
#include <syscall.h>
#endif

#define DEFAULT_HASH_SIZE	32
#define DEFAULT_MIN_ALLOC_SIZE	1
#define DEFAULT_RAND_POOL	1000000

#define TEST_HASH_SEED	0x42UL

/* Make this big enough to include the POWER5+ L3 cacheline size of 256B */
#define CACHE_LINE_SIZE 4096

/* hardcoded number of CPUs */
#define NR_CPUS 16384

#ifdef POISON_FREE
#define poison_free(ptr)				\
	do {						\
		memset(ptr, 0x42, sizeof(*(ptr)));	\
		free(ptr);				\
	} while (0)
#else
#define poison_free(ptr)	free(ptr)
#endif



#if defined(_syscall0)
_syscall0(pid_t, gettid)
#elif defined(__NR_gettid)
static inline pid_t gettid(void)
{
	return syscall(__NR_gettid);
}
#else
#warning "use pid as tid"
static inline pid_t gettid(void)
{
	return getpid();
}
#endif

#ifndef DYNAMIC_LINK_TEST
#define _LGPL_SOURCE
#else
#define debug_yield_read()
#endif
#include <urcu-qsbr.h>
#include <urcu/rculfhash.h>
#include <urcu-call-rcu.h>

struct wr_count {
	unsigned long update_ops;
	unsigned long add;
	unsigned long add_exist;
	unsigned long remove;
};

static unsigned int __thread rand_lookup;
static unsigned long __thread nr_add;
static unsigned long __thread nr_addexist;
static unsigned long __thread nr_del;
static unsigned long __thread nr_delnoent;
static unsigned long __thread lookup_fail;
static unsigned long __thread lookup_ok;

static struct cds_lfht *test_ht;

struct test_data {
	int a;
	int b;
};

struct lfht_test_node {
	struct cds_lfht_node node;
	void *key;
	unsigned int key_len;
	/* cache-cold for iteration */
	struct rcu_head head;
};

static inline struct lfht_test_node *
to_test_node(struct cds_lfht_node *node)
{
	return caa_container_of(node, struct lfht_test_node, node);
}

static inline
void lfht_test_node_init(struct lfht_test_node *node, void *key,
			size_t key_len)
{
	cds_lfht_node_init(&node->node);
	node->key = key;
	node->key_len = key_len;
}

static inline struct lfht_test_node *
cds_lfht_iter_get_test_node(struct cds_lfht_iter *iter)
{
	return to_test_node(cds_lfht_iter_get_node(iter));
}

static volatile int test_go, test_stop;

static unsigned long wdelay;

static unsigned long duration;

/* read-side C.S. duration, in loops */
static unsigned long rduration;

static unsigned long init_hash_size = DEFAULT_HASH_SIZE;
static unsigned long min_hash_alloc_size = DEFAULT_MIN_ALLOC_SIZE;
static unsigned long max_hash_buckets_size = (1UL << 20);
static unsigned long init_populate;
static int opt_auto_resize;
static int add_only, add_unique, add_replace;
static const struct cds_lfht_mm_type *memory_backend;

static unsigned long init_pool_offset, lookup_pool_offset, write_pool_offset;
static unsigned long init_pool_size = DEFAULT_RAND_POOL,
	lookup_pool_size = DEFAULT_RAND_POOL,
	write_pool_size = DEFAULT_RAND_POOL;
static int validate_lookup;

static int count_pipe[2];

static inline void loop_sleep(unsigned long l)
{
	while(l-- != 0)
		caa_cpu_relax();
}

static int verbose_mode;

#define printf_verbose(fmt, args...)		\
	do {					\
		if (verbose_mode)		\
			printf(fmt, ## args);	\
	} while (0)

static unsigned int cpu_affinities[NR_CPUS];
static unsigned int next_aff = 0;
static int use_affinity = 0;

pthread_mutex_t affinity_mutex = PTHREAD_MUTEX_INITIALIZER;

static void set_affinity(void)
{
	cpu_set_t mask;
	int cpu;
	int ret;

	if (!use_affinity)
		return;

	ret = pthread_mutex_lock(&affinity_mutex);
	if (ret) {
		perror("Error in pthread mutex lock");
		exit(-1);
	}
	cpu = cpu_affinities[next_aff++];
	ret = pthread_mutex_unlock(&affinity_mutex);
	if (ret) {
		perror("Error in pthread mutex unlock");
		exit(-1);
	}
	CPU_ZERO(&mask);
	CPU_SET(cpu, &mask);
	sched_setaffinity(0, sizeof(mask), &mask);
}

static enum {
	AR_RANDOM = 0,
	AR_ADD = 1,
	AR_REMOVE = -1,
} addremove;	/* 1: add, -1 remove, 0: random */

static
void sigusr1_handler(int signo)
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

static
void sigusr2_handler(int signo)
{
	char msg[1] = { 0x42 };
	ssize_t ret;

	do {
		ret = write(count_pipe[1], msg, 1);	/* wakeup thread */
	} while (ret == -1L && errno == EINTR);
}

/*
 * returns 0 if test should end.
 */
static int test_duration_write(void)
{
	return !test_stop;
}

static int test_duration_read(void)
{
	return !test_stop;
}

static unsigned long long __thread nr_writes;
static unsigned long long __thread nr_reads;

static unsigned int nr_readers;
static unsigned int nr_writers;

pthread_mutex_t rcu_copy_mutex = PTHREAD_MUTEX_INITIALIZER;

void rcu_copy_mutex_lock(void)
{
	int ret;
	ret = pthread_mutex_lock(&rcu_copy_mutex);
	if (ret) {
		perror("Error in pthread mutex lock");
		exit(-1);
	}
}

void rcu_copy_mutex_unlock(void)
{
	int ret;

	ret = pthread_mutex_unlock(&rcu_copy_mutex);
	if (ret) {
		perror("Error in pthread mutex unlock");
		exit(-1);
	}
}

/*
 * Hash function
 * Source: http://burtleburtle.net/bob/c/lookup3.c
 * Originally Public Domain
 */

#define rot(x, k) (((x) << (k)) | ((x) >> (32 - (k))))

#define mix(a, b, c) \
do { \
	a -= c; a ^= rot(c,  4); c += b; \
	b -= a; b ^= rot(a,  6); a += c; \
	c -= b; c ^= rot(b,  8); b += a; \
	a -= c; a ^= rot(c, 16); c += b; \
	b -= a; b ^= rot(a, 19); a += c; \
	c -= b; c ^= rot(b,  4); b += a; \
} while (0)

#define final(a, b, c) \
{ \
	c ^= b; c -= rot(b, 14); \
	a ^= c; a -= rot(c, 11); \
	b ^= a; b -= rot(a, 25); \
	c ^= b; c -= rot(b, 16); \
	a ^= c; a -= rot(c,  4);\
	b ^= a; b -= rot(a, 14); \
	c ^= b; c -= rot(b, 24); \
}

static __attribute__((unused))
uint32_t hash_u32(
	const uint32_t *k,	/* the key, an array of uint32_t values */
	size_t length,		/* the length of the key, in uint32_ts */
	uint32_t initval)	/* the previous hash, or an arbitrary value */
{
	uint32_t a, b, c;

	/* Set up the internal state */
	a = b = c = 0xdeadbeef + (((uint32_t) length) << 2) + initval;

	/*----------------------------------------- handle most of the key */
	while (length > 3) {
		a += k[0];
		b += k[1];
		c += k[2];
		mix(a, b, c);
		length -= 3;
		k += 3;
	}

	/*----------------------------------- handle the last 3 uint32_t's */
	switch (length) {	/* all the case statements fall through */
	case 3: c += k[2];
	case 2: b += k[1];
	case 1: a += k[0];
		final(a, b, c);
	case 0:			/* case 0: nothing left to add */
		break;
	}
	/*---------------------------------------------- report the result */
	return c;
}

static
void hashword2(
	const uint32_t *k,	/* the key, an array of uint32_t values */
	size_t length,		/* the length of the key, in uint32_ts */
	uint32_t *pc,		/* IN: seed OUT: primary hash value */
	uint32_t *pb)		/* IN: more seed OUT: secondary hash value */
{
	uint32_t a, b, c;

	/* Set up the internal state */
	a = b = c = 0xdeadbeef + ((uint32_t) (length << 2)) + *pc;
	c += *pb;

	/*----------------------------------------- handle most of the key */
	while (length > 3) {
		a += k[0];
		b += k[1];
		c += k[2];
		mix(a, b, c);
		length -= 3;
		k += 3;
	}

	/*----------------------------------- handle the last 3 uint32_t's */
	switch (length) {	/* all the case statements fall through */
	case 3: c += k[2];
	case 2: b += k[1];
	case 1: a += k[0];
		final(a, b, c);
	case 0:			/* case 0: nothing left to add */
		break;
	}
	/*---------------------------------------------- report the result */
	*pc = c;
	*pb = b;
}

#if (CAA_BITS_PER_LONG == 32)
static
unsigned long test_hash(const void *_key, size_t length, unsigned long seed)
{
	unsigned int key = (unsigned int) _key;

	assert(length == sizeof(unsigned int));
	return hash_u32(&key, 1, seed);
}
#else
static
unsigned long test_hash(const void *_key, size_t length, unsigned long seed)
{
	union {
		uint64_t v64;
		uint32_t v32[2];
	} v;
	union {
		uint64_t v64;
		uint32_t v32[2];
	} key;

	assert(length == sizeof(unsigned long));
	v.v64 = (uint64_t) seed;
	key.v64 = (uint64_t) _key;
	hashword2(key.v32, 2, &v.v32[0], &v.v32[1]);
	return v.v64;
}
#endif

static
unsigned long test_compare(const void *key1, size_t key1_len,
                           const void *key2, size_t key2_len)
{
	if (caa_unlikely(key1_len != key2_len))
		return -1;
	assert(key1_len == sizeof(unsigned long));
	if (key1 == key2)
		return 0;
	else
		return 1;
}

static
int test_match(struct cds_lfht_node *node, const void *key)
{
	struct lfht_test_node *test_node = to_test_node(node);

	return !test_compare(test_node->key, test_node->key_len,
			key, sizeof(unsigned long));
}

static inline
void cds_lfht_test_lookup(struct cds_lfht *ht, void *key, size_t key_len,
		struct cds_lfht_iter *iter)
{
	assert(key_len == sizeof(unsigned long));

	cds_lfht_lookup(ht, test_hash(key, key_len, TEST_HASH_SEED),
			test_match, key, iter);
}

void *thr_count(void *arg)
{
	printf_verbose("thread_begin %s, thread id : %lx, tid %lu\n",
			"counter", pthread_self(), (unsigned long)gettid());

	rcu_register_thread();

	for (;;) {
		unsigned long count;
		long approx_before, approx_after;
		ssize_t len;
		char buf[1];

		rcu_thread_offline();
		len = read(count_pipe[0], buf, 1);
		rcu_thread_online();
		if (caa_unlikely(!test_duration_read()))
			break;
		if (len != 1)
			continue;
		/* Accounting */
		printf("Counting nodes... ");
		fflush(stdout);
		rcu_read_lock();
		cds_lfht_count_nodes(test_ht, &approx_before, &count,
				&approx_after);
		rcu_read_unlock();
		printf("done.\n");
		printf("Approximation before node accounting: %ld nodes.\n",
			approx_before);
		printf("Accounting of nodes in the hash table: "
			"%lu nodes.\n",
			count);
		printf("Approximation after node accounting: %ld nodes.\n",
			approx_after);
	}
	rcu_unregister_thread();
	return NULL;
}

void *thr_reader(void *_count)
{
	unsigned long long *count = _count;
	struct lfht_test_node *node;
	struct cds_lfht_iter iter;

	printf_verbose("thread_begin %s, thread id : %lx, tid %lu\n",
			"reader", pthread_self(), (unsigned long)gettid());

	set_affinity();

	rcu_register_thread();

	while (!test_go)
	{
	}
	cmm_smp_mb();

	for (;;) {
		rcu_read_lock();
		cds_lfht_test_lookup(test_ht,
			(void *)(((unsigned long) rand_r(&rand_lookup) % lookup_pool_size) + lookup_pool_offset),
			sizeof(void *), &iter);
		node = cds_lfht_iter_get_test_node(&iter);
		if (node == NULL) {
			if (validate_lookup) {
				printf("[ERROR] Lookup cannot find initial node.\n");
				exit(-1);
			}
			lookup_fail++;
		} else {
			lookup_ok++;
		}
		debug_yield_read();
		if (caa_unlikely(rduration))
			loop_sleep(rduration);
		rcu_read_unlock();
		nr_reads++;
		if (caa_unlikely(!test_duration_read()))
			break;
		if (caa_unlikely((nr_reads & ((1 << 10) - 1)) == 0))
			rcu_quiescent_state();
	}

	rcu_unregister_thread();

	*count = nr_reads;
	printf_verbose("thread_end %s, thread id : %lx, tid %lu\n",
			"reader", pthread_self(), (unsigned long)gettid());
	printf_verbose("readid : %lx, lookupfail %lu, lookupok %lu\n",
			pthread_self(), lookup_fail, lookup_ok);
	return ((void*)1);

}

static
void free_node_cb(struct rcu_head *head)
{
	struct lfht_test_node *node =
		caa_container_of(head, struct lfht_test_node, head);
	free(node);
}

void *thr_writer(void *_count)
{
	struct lfht_test_node *node;
	struct cds_lfht_node *ret_node;
	struct cds_lfht_iter iter;
	struct wr_count *count = _count;
	int ret;

	printf_verbose("thread_begin %s, thread id : %lx, tid %lu\n",
			"writer", pthread_self(), (unsigned long)gettid());

	set_affinity();

	rcu_register_thread();

	while (!test_go)
	{
	}
	cmm_smp_mb();

	for (;;) {
		if ((addremove == AR_ADD || add_only)
				|| (addremove == AR_RANDOM && rand_r(&rand_lookup) & 1)) {
			node = malloc(sizeof(struct lfht_test_node));
			lfht_test_node_init(node,
				(void *)(((unsigned long) rand_r(&rand_lookup) % write_pool_size) + write_pool_offset),
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
				nr_addexist++;
			} else {
				if (add_replace && ret_node) {
					call_rcu(&to_test_node(ret_node)->head,
							free_node_cb);
					nr_addexist++;
				} else {
					nr_add++;
				}
			}
		} else {
			/* May delete */
			rcu_read_lock();
			cds_lfht_test_lookup(test_ht,
				(void *)(((unsigned long) rand_r(&rand_lookup) % write_pool_size) + write_pool_offset),
				sizeof(void *), &iter);
			ret = cds_lfht_del(test_ht, &iter);
			rcu_read_unlock();
			if (ret == 0) {
				node = cds_lfht_iter_get_test_node(&iter);
				call_rcu(&node->head, free_node_cb);
				nr_del++;
			} else
				nr_delnoent++;
		}
#if 0
		//if (nr_writes % 100000 == 0) {
		if (nr_writes % 1000 == 0) {
			rcu_read_lock();
			if (rand_r(&rand_lookup) & 1) {
				ht_resize(test_ht, 1);
			} else {
				ht_resize(test_ht, -1);
			}
			rcu_read_unlock();
		}
#endif //0
		nr_writes++;
		if (caa_unlikely(!test_duration_write()))
			break;
		if (caa_unlikely(wdelay))
			loop_sleep(wdelay);
		if (caa_unlikely((nr_writes & ((1 << 10) - 1)) == 0))
			rcu_quiescent_state();
	}

	rcu_unregister_thread();

	printf_verbose("thread_end %s, thread id : %lx, tid %lu\n",
			"writer", pthread_self(), (unsigned long)gettid());
	printf_verbose("info id %lx: nr_add %lu, nr_addexist %lu, nr_del %lu, "
			"nr_delnoent %lu\n", pthread_self(), nr_add,
			nr_addexist, nr_del, nr_delnoent);
	count->update_ops = nr_writes;
	count->add = nr_add;
	count->add_exist = nr_addexist;
	count->remove = nr_del;
	return ((void*)2);
}

static int populate_hash(void)
{
	struct lfht_test_node *node;
	struct cds_lfht_node *ret_node;

	if (!init_populate)
		return 0;

	if ((add_unique || add_replace) && init_populate * 10 > init_pool_size) {
		printf("WARNING: required to populate %lu nodes (-k), but random "
"pool is quite small (%lu values) and we are in add_unique (-u) or add_replace (-s) mode. Try with a "
"larger random pool (-p option). This may take a while...\n", init_populate, init_pool_size);
	}

	while (nr_add < init_populate) {
		node = malloc(sizeof(struct lfht_test_node));
		lfht_test_node_init(node,
			(void *)(((unsigned long) rand_r(&rand_lookup) % init_pool_size) + init_pool_offset),
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
			nr_addexist++;
		} else {
			if (add_replace && ret_node) {
				call_rcu(&to_test_node(ret_node)->head, free_node_cb);
				nr_addexist++;
			} else {
				nr_add++;
			}
		}
		nr_writes++;
	}
	return 0;
}

static
void test_delete_all_nodes(struct cds_lfht *ht)
{
	struct cds_lfht_iter iter;
	struct lfht_test_node *node;
	unsigned long count = 0;

	cds_lfht_for_each_entry(ht, &iter, node, node) {
		int ret;

		ret = cds_lfht_del(test_ht, &iter);
		assert(!ret);
		call_rcu(&node->head, free_node_cb);
		count++;
	}
	printf("deleted %lu nodes.\n", count);
}

void show_usage(int argc, char **argv)
{
	printf("Usage : %s nr_readers nr_writers duration (s)\n", argv[0]);
#ifdef DEBUG_YIELD
	printf("        [-r] [-w] (yield reader and/or writer)\n");
#endif
	printf("        [-d delay] (writer period (us))\n");
	printf("        [-c duration] (reader C.S. duration (in loops))\n");
	printf("        [-v] (verbose output)\n");
	printf("        [-a cpu#] [-a cpu#]... (affinity)\n");
	printf("        [-h size] (initial number of buckets)\n");
	printf("        [-m size] (minimum number of allocated buckets)\n");
	printf("        [-n size] (maximum number of buckets)\n");
	printf("        [not -u nor -s] Add entries (supports redundant keys).\n");
	printf("        [-u] Uniquify add (no redundant keys).\n");
	printf("        [-s] Replace (swap) entries.\n");
	printf("        [-i] Add only (no removal).\n");
	printf("        [-k nr_nodes] Number of nodes to insert initially.\n");
	printf("        [-A] Automatically resize hash table.\n");
	printf("        [-B order|chunk|mmap] Specify the memory backend.\n");
	printf("        [-R offset] Lookup pool offset.\n");
	printf("        [-S offset] Write pool offset.\n");
	printf("        [-T offset] Init pool offset.\n");
	printf("        [-M size] Lookup pool size.\n");
	printf("        [-N size] Write pool size.\n");
	printf("        [-O size] Init pool size.\n");
	printf("        [-V] Validate lookups of init values (use with filled init pool, same lookup range, with different write range).\n");
	printf("\n\n");
}

int main(int argc, char **argv)
{
	int err;
	pthread_t *tid_reader, *tid_writer;
	pthread_t tid_count;
	void *tret;
	unsigned long long *count_reader;
	struct wr_count *count_writer;
	unsigned long long tot_reads = 0, tot_writes = 0,
		tot_add = 0, tot_add_exist = 0, tot_remove = 0;
	unsigned long count;
	long approx_before, approx_after;
	int i, a, ret;
	struct sigaction act;
	unsigned int remain;

	if (argc < 4) {
		show_usage(argc, argv);
		return -1;
	}

	err = sscanf(argv[1], "%u", &nr_readers);
	if (err != 1) {
		show_usage(argc, argv);
		return -1;
	}

	err = sscanf(argv[2], "%u", &nr_writers);
	if (err != 1) {
		show_usage(argc, argv);
		return -1;
	}
	
	err = sscanf(argv[3], "%lu", &duration);
	if (err != 1) {
		show_usage(argc, argv);
		return -1;
	}

	for (i = 4; i < argc; i++) {
		if (argv[i][0] != '-')
			continue;
		switch (argv[i][1]) {
#ifdef DEBUG_YIELD
		case 'r':
			yield_active |= YIELD_READ;
			break;
		case 'w':
			yield_active |= YIELD_WRITE;
			break;
#endif
		case 'a':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			a = atoi(argv[++i]);
			cpu_affinities[next_aff++] = a;
			use_affinity = 1;
			printf_verbose("Adding CPU %d affinity\n", a);
			break;
		case 'c':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			rduration = atol(argv[++i]);
			break;
		case 'd':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			wdelay = atol(argv[++i]);
			break;
		case 'v':
			verbose_mode = 1;
			break;
		case 'h':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			init_hash_size = atol(argv[++i]);
			break;
		case 'm':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			min_hash_alloc_size = atol(argv[++i]);
			break;
		case 'n':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			max_hash_buckets_size = atol(argv[++i]);
			break;
		case 'u':
			if (add_replace) {
				printf("Please specify at most one of -s or -u.\n");
				exit(-1);
			}
			add_unique = 1;
			break;
		case 's':
			if (add_unique) {
				printf("Please specify at most one of -s or -u.\n");
				exit(-1);
			}
			add_replace = 1;
			break;
		case 'i':
			add_only = 1;
			break;
		case 'k':
			init_populate = atol(argv[++i]);
			break;
		case 'A':
			opt_auto_resize = 1;
			break;
		case 'B':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			i++;
			if (!strcmp("order", argv[i]))
				memory_backend = &cds_lfht_mm_order;
			else if (!strcmp("chunk", argv[i]))
				memory_backend = &cds_lfht_mm_chunk;
			else if (!strcmp("mmap", argv[i]))
				memory_backend = &cds_lfht_mm_mmap;
                        else {
				printf("Please specify memory backend with order|chunk|mmap.\n");
				exit(-1);
			}
			break;
		case 'R':
			lookup_pool_offset = atol(argv[++i]);
			break;
		case 'S':
			write_pool_offset = atol(argv[++i]);
			break;
		case 'T':
			init_pool_offset = atol(argv[++i]);
			break;
		case 'M':
			lookup_pool_size = atol(argv[++i]);
			break;
		case 'N':
			write_pool_size = atol(argv[++i]);
			break;
		case 'O':
			init_pool_size = atol(argv[++i]);
			break;
		case 'V':
			validate_lookup = 1;
			break;

		}
	}

	/* Check if hash size is power of 2 */
	if (init_hash_size && init_hash_size & (init_hash_size - 1)) {
		printf("Error: Initial number of buckets (%lu) is not a power of 2.\n",
			init_hash_size);
		return -1;
	}

	if (min_hash_alloc_size && min_hash_alloc_size & (min_hash_alloc_size - 1)) {
		printf("Error: Minimum number of allocated buckets (%lu) is not a power of 2.\n",
			min_hash_alloc_size);
		return -1;
	}

	if (max_hash_buckets_size && max_hash_buckets_size & (max_hash_buckets_size - 1)) {
		printf("Error: Maximum number of buckets (%lu) is not a power of 2.\n",
			max_hash_buckets_size);
		return -1;
	}

	memset(&act, 0, sizeof(act));
	ret = sigemptyset(&act.sa_mask);
	if (ret == -1) {
		perror("sigemptyset");
		return -1;
	}
	act.sa_handler = sigusr1_handler;
	act.sa_flags = SA_RESTART;
	ret = sigaction(SIGUSR1, &act, NULL);
	if (ret == -1) {
		perror("sigaction");
		return -1;
	}

	ret = pipe(count_pipe);
	if (ret == -1) {
		perror("pipe");
		return -1;
	}

	/* spawn counter thread */
	err = pthread_create(&tid_count, NULL, thr_count,
			     NULL);
	if (err != 0)
		exit(1);

	act.sa_handler = sigusr2_handler;
	act.sa_flags = SA_RESTART;
	ret = sigaction(SIGUSR2, &act, NULL);
	if (ret == -1) {
		perror("sigaction");
		return -1;
	}

	printf_verbose("running test for %lu seconds, %u readers, %u writers.\n",
		duration, nr_readers, nr_writers);
	printf_verbose("Writer delay : %lu loops.\n", wdelay);
	printf_verbose("Reader duration : %lu loops.\n", rduration);
	printf_verbose("Mode:%s%s.\n",
		add_only ? " add only" : " add/remove",
		add_unique ? " uniquify" : ( add_replace ? " replace" : " insert"));
	printf_verbose("Initial number of buckets: %lu buckets.\n", init_hash_size);
	printf_verbose("Minimum number of allocated buckets: %lu buckets.\n", min_hash_alloc_size);
	printf_verbose("Maximum number of buckets: %lu buckets.\n", max_hash_buckets_size);
	printf_verbose("Init pool size offset %lu size %lu.\n",
		init_pool_offset, init_pool_size);
	printf_verbose("Lookup pool size offset %lu size %lu.\n",
		lookup_pool_offset, lookup_pool_size);
	printf_verbose("Update pool size offset %lu size %lu.\n",
		write_pool_offset, write_pool_size);
	printf_verbose("thread %-6s, thread id : %lx, tid %lu\n",
			"main", pthread_self(), (unsigned long)gettid());

	tid_reader = malloc(sizeof(*tid_reader) * nr_readers);
	tid_writer = malloc(sizeof(*tid_writer) * nr_writers);
	count_reader = malloc(sizeof(*count_reader) * nr_readers);
	count_writer = malloc(sizeof(*count_writer) * nr_writers);

	err = create_all_cpu_call_rcu_data(0);
        assert(!err);

	if (memory_backend) {
		test_ht = _cds_lfht_new(init_hash_size, min_hash_alloc_size,
				max_hash_buckets_size,
				(opt_auto_resize ? CDS_LFHT_AUTO_RESIZE : 0) |
				CDS_LFHT_ACCOUNTING, memory_backend,
				&rcu_flavor, NULL);
	} else {
		test_ht = cds_lfht_new(init_hash_size, min_hash_alloc_size,
				max_hash_buckets_size,
				(opt_auto_resize ? CDS_LFHT_AUTO_RESIZE : 0) |
				CDS_LFHT_ACCOUNTING, NULL);
	}

	/*
	 * Hash Population needs to be seen as a RCU reader
	 * thread from the point of view of resize.
	 */
	rcu_register_thread();
      	ret = populate_hash();
	assert(!ret);

	rcu_thread_offline();

	next_aff = 0;

	for (i = 0; i < nr_readers; i++) {
		err = pthread_create(&tid_reader[i], NULL, thr_reader,
				     &count_reader[i]);
		if (err != 0)
			exit(1);
	}
	for (i = 0; i < nr_writers; i++) {
		err = pthread_create(&tid_writer[i], NULL, thr_writer,
				     &count_writer[i]);
		if (err != 0)
			exit(1);
	}

	cmm_smp_mb();

	test_go = 1;

	remain = duration;
	do {
		remain = sleep(remain);
	} while (remain > 0);

	test_stop = 1;

	for (i = 0; i < nr_readers; i++) {
		err = pthread_join(tid_reader[i], &tret);
		if (err != 0)
			exit(1);
		tot_reads += count_reader[i];
	}
	for (i = 0; i < nr_writers; i++) {
		err = pthread_join(tid_writer[i], &tret);
		if (err != 0)
			exit(1);
		tot_writes += count_writer[i].update_ops;
		tot_add += count_writer[i].add;
		tot_add_exist += count_writer[i].add_exist;
		tot_remove += count_writer[i].remove;
	}

	/* teardown counter thread */
	act.sa_handler = SIG_IGN;
	act.sa_flags = SA_RESTART;
	ret = sigaction(SIGUSR2, &act, NULL);
	if (ret == -1) {
		perror("sigaction");
		return -1;
	}
	{
		char msg[1] = { 0x42 };
		ssize_t ret;

		do {
			ret = write(count_pipe[1], msg, 1);	/* wakeup thread */
		} while (ret == -1L && errno == EINTR);
	}
	err = pthread_join(tid_count, &tret);
	if (err != 0)
		exit(1);

	fflush(stdout);
	rcu_thread_online();
	rcu_read_lock();
	printf("Counting nodes... ");
	cds_lfht_count_nodes(test_ht, &approx_before, &count, &approx_after);
	printf("done.\n");
	test_delete_all_nodes(test_ht);
	rcu_read_unlock();
	rcu_thread_offline();
	if (count) {
		printf("Approximation before node accounting: %ld nodes.\n",
			approx_before);
		printf("Nodes deleted from hash table before destroy: "
			"%lu nodes.\n",
			count);
		printf("Approximation after node accounting: %ld nodes.\n",
			approx_after);
	}
	ret = cds_lfht_destroy(test_ht, NULL);
	if (ret)
		printf_verbose("final delete aborted\n");
	else
		printf_verbose("final delete success\n");
	printf_verbose("total number of reads : %llu, writes %llu\n", tot_reads,
	       tot_writes);
	printf("SUMMARY %-25s testdur %4lu nr_readers %3u rdur %6lu "
		"nr_writers %3u "
		"wdelay %6lu nr_reads %12llu nr_writes %12llu nr_ops %12llu "
		"nr_add %12llu nr_add_fail %12llu nr_remove %12llu nr_leaked %12lld\n",
		argv[0], duration, nr_readers, rduration,
		nr_writers, wdelay, tot_reads, tot_writes,
		tot_reads + tot_writes, tot_add, tot_add_exist, tot_remove,
		(long long) tot_add + init_populate - tot_remove - count);
	rcu_unregister_thread();
	free_all_cpu_call_rcu_data();
	free(tid_reader);
	free(tid_writer);
	free(count_reader);
	free(count_writer);
	return 0;
}
