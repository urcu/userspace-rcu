/*
 * test_urcu.c
 *
 * Userspace RCU library - test program
 *
 * Copyright February 2009 - Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
 *
 * Distributed under GPLv2
 */

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

#include "urcu.h"

struct test_array {
	int a;
};

static struct test_array *test_rcu_pointer;

static unsigned long duration;
static time_t start_time;
static unsigned long __thread duration_interval;
#define DURATION_TEST_DELAY 100

/*
 * returns 0 if test should end.
 */
static int test_duration(void)
{
	if (duration_interval++ >= DURATION_TEST_DELAY) {
		duration_interval = 0;
		if (time(NULL) - start_time >= duration)
			return 0;
	}
	return 1;
}

#define NR_READ 10
#define NR_WRITE 9

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

void *thr_reader(void *arg)
{
	int qparity;
	struct test_array *local_ptr;

	printf("thread_begin %s, thread id : %lx, tid %lu\n",
			"reader", pthread_self(), (unsigned long)gettid());

	urcu_register_thread();

	for (;;) {
		rcu_read_lock(&qparity);
		local_ptr = rcu_dereference(test_rcu_pointer);
		if (local_ptr)
			assert(local_ptr->a == 8);
		rcu_read_unlock(&qparity);
		if (!test_duration())
			break;
	}

	urcu_unregister_thread();

	printf("thread_end %s, thread id : %lx, tid %lu\n",
			"reader", pthread_self(), (unsigned long)gettid());
	return ((void*)1);

}

void *thr_writer(void *arg)
{
	struct test_array *new, *old;

	printf("thread_begin %s, thread id : %lx, tid %lu\n",
			"writer", pthread_self(), (unsigned long)gettid());

	for (;;) {
		new = malloc(sizeof(struct test_array));
		rcu_copy_mutex_lock();
		old = test_rcu_pointer;
		if (old)
			assert(old->a == 8);
		new->a = 8;
		old = urcu_publish_content((void **)&test_rcu_pointer, new);
		rcu_copy_mutex_unlock();
		/* can be done after unlock */
		if (old)
			old->a = 0;
		free(old);
		if (!test_duration())
			break;
		usleep(1);
	}

	printf("thread_end %s, thread id : %lx, tid %lu\n",
			"writer", pthread_self(), (unsigned long)gettid());
	return ((void*)2);
}

int main(int argc, char **argv)
{
	int err;
	pthread_t tid_reader[NR_READ], tid_writer[NR_WRITE];
	void *tret;
	int i;

	if (argc < 2) {
		printf("Usage : %s duration (s) [-r] [-w] "
		       "(yield reader and/or writer)\n", argv[0]);
		return -1;
	}

	err = sscanf(argv[1], "%lu", &duration);
	if (err != 1) {
		printf("Usage : %s duration (s) [-r] [-w] "
		       "(yield reader and/or writer)\n", argv[0]);
		return -1;
	}

#ifdef DEBUG_YIELD
	for (i = 2; i < argc; i++) {
		if (argv[i][0] != '-')
			continue;
		switch (argv[i][1]) {
		case 'r':
			yield_active |= YIELD_READ;
			break;
		case 'w':
			yield_active |= YIELD_WRITE;
			break;
		}
	}
#endif

	printf("running test for %lu seconds.\n", duration);
	start_time = time(NULL);
	printf("thread %-6s, thread id : %lx, tid %lu\n",
			"main", pthread_self(), (unsigned long)gettid());

	for (i = 0; i < NR_READ; i++) {
		err = pthread_create(&tid_reader[i], NULL, thr_reader, NULL);
		if (err != 0)
			exit(1);
	}
	for (i = 0; i < NR_WRITE; i++) {
		err = pthread_create(&tid_writer[i], NULL, thr_writer, NULL);
		if (err != 0)
			exit(1);
	}

	for (i = 0; i < NR_READ; i++) {
		err = pthread_join(tid_reader[i], &tret);
		if (err != 0)
			exit(1);
	}
	for (i = 0; i < NR_WRITE; i++) {
		err = pthread_join(tid_writer[i], &tret);
		if (err != 0)
			exit(1);
	}
	free(test_rcu_pointer);

	return 0;
}
