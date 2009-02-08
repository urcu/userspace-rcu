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
	int b;
	char c[200];
};

static struct test_array *test_rcu_pointer;

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
	int qparity, i, j;
	struct test_array *local_ptr;

	printf("thread %s, thread id : %lx, tid %lu\n",
			"reader", pthread_self(), (unsigned long)gettid());
	sleep(2);

	urcu_register_thread();

	for (i = 0; i < 100000; i++) {
		for (j = 0; j < 100000000; j++) {
			rcu_read_lock(&qparity);
			local_ptr = rcu_dereference(test_rcu_pointer);
			if (local_ptr) {
				assert(local_ptr->a == 8);
				assert(local_ptr->b == 12);
				assert(local_ptr->c[55] == 2);
			}
			rcu_read_unlock(&qparity);
		}
	}

	urcu_unregister_thread();

	return ((void*)1);

}

void *thr_writer(void *arg)
{
	int i;
	struct test_array *new, *old;

	printf("thread %s, thread id : %lx, tid %lu\n",
			"writer", pthread_self(), (unsigned long)gettid());
	sleep(2);

	for (i = 0; i < 10000000; i++) {
		new = malloc(sizeof(struct test_array));
		rcu_copy_mutex_lock();
		old = test_rcu_pointer;
		if (old) {
			assert(old->a == 8);
			assert(old->b == 12);
			assert(old->c[55] == 2);
		}
		new->c[55] = 2;
		new->b = 12;
		new->a = 8;
		old = urcu_publish_content((void **)&test_rcu_pointer, new);
		rcu_copy_mutex_unlock();
		/* can be done after unlock */
		if (old) {
			old->a = 0;
			old->b = 0;
			old->c[55] = 0;
		}
		free(old);
		usleep(1);
	}

	return ((void*)2);
}

int main()
{
	int err;
	pthread_t tid_reader[NR_READ], tid_writer[NR_WRITE];
	void *tret;
	int i;

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

	sleep(10);

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
