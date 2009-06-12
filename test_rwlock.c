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

#ifndef DYNAMIC_LINK_TEST
#define _LGPL_SOURCE
#else
#define debug_yield_read()
#endif
#include "urcu.h"

struct test_array {
	int a;
};

pthread_rwlock_t lock = PTHREAD_RWLOCK_INITIALIZER;

static volatile int test_go, test_stop;

static int wdelay;

static volatile struct test_array test_array = { 8 };

static unsigned long duration;

/* read-side C.S. duration, in loops */
static unsigned long rduration;

static inline void loop_sleep(unsigned long l)
{
	while(l-- != 0)
		cpu_relax();
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

void *thr_reader(void *_count)
{
	unsigned long long *count = _count;

	printf("thread_begin %s, thread id : %lx, tid %lu\n",
			"reader", pthread_self(), (unsigned long)gettid());

	while (!test_go)
	{
	}

	for (;;) {
		pthread_rwlock_rdlock(&lock);
		assert(test_array.a == 8);
		if (unlikely(rduration))
			loop_sleep(rduration);
		pthread_rwlock_unlock(&lock);
		nr_reads++;
		if (unlikely(!test_duration_read()))
			break;
	}

	*count = nr_reads;
	printf("thread_end %s, thread id : %lx, tid %lu\n",
			"reader", pthread_self(), (unsigned long)gettid());
	return ((void*)1);

}

void *thr_writer(void *_count)
{
	unsigned long long *count = _count;

	printf("thread_begin %s, thread id : %lx, tid %lu\n",
			"writer", pthread_self(), (unsigned long)gettid());

	while (!test_go)
	{
	}
	smp_mb();

	for (;;) {
		pthread_rwlock_wrlock(&lock);
		test_array.a = 0;
		test_array.a = 8;
		pthread_rwlock_unlock(&lock);
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
	printf(" [-c duration] (reader C.S. duration (in loops))");
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
	smp_mb();

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
	printf("Reader duration : %lu loops.\n", rduration);
	printf("thread %-6s, thread id : %lx, tid %lu\n",
			"main", pthread_self(), (unsigned long)gettid());
	if (use_affinity
	    && sched_setaffinity(0, sizeof(affinity), &affinity) < 0) {
		perror("sched_setaffinity");
		exit(-1);
	}

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
	free(tid_reader);
	free(tid_writer);
	free(count_reader);
	free(count_writer);
	return 0;
}
