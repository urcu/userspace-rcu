/*
 * test_ht.c
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
#define DEFAULT_RAND_POOL	1000000

/* Make this big enough to include the POWER5+ L3 cacheline size of 256B */
#define CACHE_LINE_SIZE 4096

/* hardcoded number of CPUs */
#define NR_CPUS 16384

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

static volatile int test_go, test_stop;

static unsigned long wdelay;

static unsigned long duration;

/* read-side C.S. duration, in loops */
static unsigned long rduration;

static unsigned long init_hash_size = DEFAULT_HASH_SIZE;
static unsigned long rand_pool = DEFAULT_RAND_POOL;
static int add_only, add_unique;

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
unsigned long test_hash(void *_key, size_t length, unsigned long seed)
{
	unsigned long key = (unsigned long) _key;
	unsigned long v;

	assert(length == sizeof(unsigned long));
	return hash_u32(&v, 1, seed);
}
#else
static
unsigned long test_hash(void *_key, size_t length, unsigned long seed)
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
unsigned long test_compare(void *key1, size_t key1_len,
                           void *key2, size_t key2_len)
{
	if (unlikely(key1_len != key2_len))
		return -1;
	assert(key1_len == sizeof(unsigned long));
	if (key1 == key2)
		return 0;
	else
		return 1;
}

void *thr_reader(void *_count)
{
	unsigned long long *count = _count;
	struct cds_lfht_node *node;

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
		node = cds_lfht_lookup(test_ht,
			(void *)(unsigned long)(rand_r(&rand_lookup) % rand_pool),
			sizeof(void *));
		if (node == NULL)
			lookup_fail++;
		else
			lookup_ok++;
		debug_yield_read();
		if (unlikely(rduration))
			loop_sleep(rduration);
		rcu_read_unlock();
		nr_reads++;
		if (unlikely(!test_duration_read()))
			break;
		if (unlikely((nr_reads & ((1 << 10) - 1)) == 0))
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
	struct cds_lfht_node *node =
		caa_container_of(head, struct cds_lfht_node, head);
	free(node);
}

void *thr_writer(void *_count)
{
	struct cds_lfht_node *node, *ret_node;
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
		if (add_only || rand_r(&rand_lookup) & 1) {
			node = malloc(sizeof(struct cds_lfht_node));
			rcu_read_lock();
			cds_lfht_node_init(node,
				(void *)(unsigned long)(rand_r(&rand_lookup) % rand_pool),
				sizeof(void *));
			if (add_unique)
				ret_node = cds_lfht_add_unique(test_ht, node);
			else
				cds_lfht_add(test_ht, node);
			rcu_read_unlock();
			if (add_unique && ret_node != node) {
				free(node);
				nr_addexist++;
			} else
				nr_add++;
		} else {
			/* May delete */
			rcu_read_lock();
			node = cds_lfht_lookup(test_ht,
				(void *)(unsigned long)(rand_r(&rand_lookup) % rand_pool),
				sizeof(void *));
			if (node)
				ret = cds_lfht_remove(test_ht, node);
			else
				ret = -ENOENT;
			rcu_read_unlock();
			if (ret == 0) {
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
		if (unlikely(!test_duration_write()))
			break;
		if (unlikely(wdelay))
			loop_sleep(wdelay);
		if (unlikely((nr_writes & ((1 << 10) - 1)) == 0))
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

void show_usage(int argc, char **argv)
{
	printf("Usage : %s nr_readers nr_writers duration (s)", argv[0]);
#ifdef DEBUG_YIELD
	printf(" [-r] [-w] (yield reader and/or writer)");
#endif
	printf(" [-d delay] (writer period (us))");
	printf(" [-c duration] (reader C.S. duration (in loops))");
	printf(" [-v] (verbose output)");
	printf(" [-a cpu#] [-a cpu#]... (affinity)");
	printf(" [-p size] (random key value pool size)");
	printf(" [-h size] (initial hash table size)");
	printf(" [-u] Uniquify add.");
	printf(" [-i] Add only (no removal).");
	printf("\n");
}

int main(int argc, char **argv)
{
	int err;
	pthread_t *tid_reader, *tid_writer;
	void *tret;
	unsigned long long *count_reader;
	struct wr_count *count_writer;
	unsigned long long tot_reads = 0, tot_writes = 0,
		tot_add = 0, tot_add_exist = 0, tot_remove = 0;
	unsigned long count, removed;
	int i, a, ret;

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
		case 'p':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			rand_pool = atol(argv[++i]);
			break;
		case 'h':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			init_hash_size = atol(argv[++i]);
			break;
		case 'u':
			add_unique = 1;
			break;
		case 'i':
			add_only = 1;
			break;
		}
	}

	/* Check if hash size is power of 2 */
	if (init_hash_size && init_hash_size & (init_hash_size - 1)) {
		printf("Error: Hash table size %lu is not a power of 2.\n",
			init_hash_size);
		return -1;
	}

	printf_verbose("running test for %lu seconds, %u readers, %u writers.\n",
		duration, nr_readers, nr_writers);
	printf_verbose("Writer delay : %lu loops.\n", wdelay);
	printf_verbose("Reader duration : %lu loops.\n", rduration);
	printf_verbose("Random pool size : %lu.\n", rand_pool);
	printf_verbose("Mode:%s%s.\n",
		add_only ? " add only" : " add/remove",
		add_unique ? " uniquify" : "");
	printf_verbose("Initial hash table size: %lu buckets.\n", init_hash_size);
	printf_verbose("thread %-6s, thread id : %lx, tid %lu\n",
			"main", pthread_self(), (unsigned long)gettid());

	tid_reader = malloc(sizeof(*tid_reader) * nr_readers);
	tid_writer = malloc(sizeof(*tid_writer) * nr_writers);
	count_reader = malloc(sizeof(*count_reader) * nr_readers);
	count_writer = malloc(sizeof(*count_writer) * nr_writers);
	test_ht = cds_lfht_new(test_hash, test_compare, 0x42UL,
			 init_hash_size, call_rcu);

        err = create_all_cpu_call_rcu_data(0);
        assert(!err);

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

	sleep(duration);

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
	printf("Counting nodes... ");
	fflush(stdout);
	cds_lfht_count_nodes(test_ht, &count, &removed);
	printf("done.\n");
	if (count || removed)
		printf("WARNING: nodes left in the hash table upon destroy: "
			"%lu nodes + %lu logically removed.\n", count, removed);
	ret = cds_lfht_destroy(test_ht);

	if (ret)
		printf_verbose("final delete aborted\n");
	else
		printf_verbose("final delete success\n");
	printf_verbose("total number of reads : %llu, writes %llu\n", tot_reads,
	       tot_writes);
	printf("SUMMARY %-25s testdur %4lu nr_readers %3u rdur %6lu "
		"nr_writers %3u "
		"wdelay %6lu rand_pool %12llu nr_reads %12llu nr_writes %12llu nr_ops %12llu "
		"nr_add %12llu nr_add_fail %12llu nr_remove %12llu nr_leaked %12llu\n",
		argv[0], duration, nr_readers, rduration,
		nr_writers, wdelay, rand_pool, tot_reads, tot_writes,
		tot_reads + tot_writes, tot_add, tot_add_exist, tot_remove,
		tot_add - tot_remove - count);
	free(tid_reader);
	free(tid_writer);
	free(count_reader);
	free(count_writer);
	return 0;
}
