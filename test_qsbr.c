/*
 * test_urcu.c
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
#include <sys/syscall.h>
#include <sched.h>

#include "arch.h"

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

#define _LGPL_SOURCE
#include "urcu-qsbr.h"

struct test_array {
	int a;
};

static volatile int test_go, test_stop;

static int wdelay;

static struct test_array *test_rcu_pointer;

static unsigned long duration;

/* read-side C.S. duration, in us */
static unsigned long rduration;

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
 * malloc/free are reusing memory areas too quickly, which does not let us
 * test races appropriately. Use a large circular array for allocations.
 * ARRAY_SIZE is larger than nr_writers, which insures we never run over our tail.
 */
#define ARRAY_SIZE (1048576 * nr_writers)
#define ARRAY_POISON 0xDEADBEEF
static int array_index;
static struct test_array *test_array;

static struct test_array *test_array_alloc(void)
{
	struct test_array *ret;
	int index;

	rcu_copy_mutex_lock();
	index = array_index % ARRAY_SIZE;
	assert(test_array[index].a == ARRAY_POISON ||
		test_array[index].a == 0);
	ret = &test_array[index];
	array_index++;
	if (array_index == ARRAY_SIZE)
		array_index = 0;
	rcu_copy_mutex_unlock();
	return ret;
}

static void test_array_free(struct test_array *ptr)
{
	if (!ptr)
		return;
	rcu_copy_mutex_lock();
	ptr->a = ARRAY_POISON;
	rcu_copy_mutex_unlock();
}

void *thr_reader(void *_count)
{
	unsigned long long *count = _count;
	struct test_array *local_ptr;

	printf("thread_begin %s, thread id : %lx, tid %lu\n",
			"reader", pthread_self(), (unsigned long)gettid());

	rcu_register_thread();

	while (!test_go)
	{
	}
	smp_mb();

	for (;;) {
		_rcu_read_lock();
		local_ptr = _rcu_dereference(test_rcu_pointer);
		debug_yield_read();
		if (local_ptr)
			assert(local_ptr->a == 8);
		if (unlikely(rduration))
			usleep(rduration);
		_rcu_read_unlock();
		nr_reads++;
		/* QS each 1024 reads */
		if (unlikely((nr_reads & ((1 << 10) - 1)) == 0))
			_rcu_quiescent_state();
		if (unlikely(!test_duration_read()))
			break;
	}

	rcu_unregister_thread();

	*count = nr_reads;
	printf("thread_end %s, thread id : %lx, tid %lu\n",
			"reader", pthread_self(), (unsigned long)gettid());
	return ((void*)1);

}

void *thr_writer(void *_count)
{
	unsigned long long *count = _count;
	struct test_array *new, *old;

	printf("thread_begin %s, thread id : %lx, tid %lu\n",
			"writer", pthread_self(), (unsigned long)gettid());

	while (!test_go)
	{
	}
	smp_mb();

	for (;;) {
		new = test_array_alloc();
		rcu_copy_mutex_lock();
		old = test_rcu_pointer;
		if (old)
			assert(old->a == 8);
		new->a = 8;
		old = _rcu_publish_content(&test_rcu_pointer, new);
		rcu_copy_mutex_unlock();
		/* can be done after unlock */
		if (old)
			old->a = 0;
		test_array_free(old);
		nr_writes++;
		if (unlikely(!test_duration_write()))
			break;
		if (unlikely(wdelay))
			usleep(wdelay);
	}

	printf("thread_end %s, thread id : %lx, tid %lu\n",
			"writer", pthread_self(), (unsigned long)gettid());
	*count = nr_writes;
	return ((void*)2);
}

void show_usage(int argc, char **argv)
{
	printf("Usage : %s nr_readers nr_writers duration (s)", argv[0]);
#ifdef DEBUG_YIELD
	printf(" [-r] [-w] (yield reader and/or writer)");
#endif
	printf(" [-d delay] (writer period (us))");
	printf(" [-c duration] (reader C.S. duration (us))");
	printf(" [-a cpu#] [-a cpu#]... (affinity)");
	printf("\n");
}

cpu_set_t affinity;

int main(int argc, char **argv)
{
	int err;
	pthread_t *tid_reader, *tid_writer;
	void *tret;
	unsigned long long *count_reader, *count_writer;
	unsigned long long tot_reads = 0, tot_writes = 0;
	int i, a;
	int use_affinity = 0;

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

	CPU_ZERO(&affinity);

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
			CPU_SET(a, &affinity);
			use_affinity = 1;
			printf("Adding CPU %d affinity\n", a);
			break;
		case 'c':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			rduration = atoi(argv[++i]);
			break;
		case 'd':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			wdelay = atoi(argv[++i]);
			break;
		}
	}

	printf("running test for %lu seconds, %u readers, %u writers.\n",
		duration, nr_readers, nr_writers);
	printf("Writer delay : %u us.\n", wdelay);
	printf("thread %-6s, thread id : %lx, tid %lu\n",
			"main", pthread_self(), (unsigned long)gettid());

	if (use_affinity
	    && sched_setaffinity(0, sizeof(affinity), &affinity) < 0) {
		perror("sched_setaffinity");
		exit(-1);
	}

	test_array = malloc(sizeof(*test_array) * ARRAY_SIZE);
	tid_reader = malloc(sizeof(*tid_reader) * nr_readers);
	tid_writer = malloc(sizeof(*tid_writer) * nr_writers);
	count_reader = malloc(sizeof(*count_reader) * nr_readers);
	count_writer = malloc(sizeof(*count_writer) * nr_writers);

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

	smp_mb();

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
		tot_writes += count_writer[i];
	}
	
	printf("total number of reads : %llu, writes %llu\n", tot_reads,
	       tot_writes);
	test_array_free(test_rcu_pointer);
	free(test_array);
	free(tid_reader);
	free(tid_writer);
	free(count_reader);
	free(count_writer);
	return 0;
}
