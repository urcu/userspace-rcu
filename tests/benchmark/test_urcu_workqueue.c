/*
 * test_urcu_workqueue.c
 *
 * Userspace RCU library - workqueue test
 *
 * Copyright February 2010-2014 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 * Copyright February 2010 - Paolo Bonzini <pbonzini@redhat.com>
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
#include "config.h"
#include <stdio.h>
#include <pthread.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <errno.h>

#include <urcu/arch.h>
#include <urcu/tls-compat.h>
#include <urcu/uatomic.h>
#include "cpuset.h"
#include "thread-id.h"

/* hardcoded number of CPUs */
#define NR_CPUS 16384

#ifndef DYNAMIC_LINK_TEST
#define _LGPL_SOURCE
#endif
#include <urcu.h>
#include <urcu/wfstack.h>
#include <urcu/workqueue-fifo.h>

static volatile int test_go, test_stop_enqueue;

static unsigned long work_loops;

static unsigned long duration;

static unsigned long dispatch_delay_loops;

static unsigned long max_queue_len;

static inline void loop_sleep(unsigned long loops)
{
	while (loops-- != 0)
		caa_cpu_relax();
}

static int verbose_mode;

static int test_wait_empty;
static int test_enqueue_stopped;

#define printf_verbose(fmt, args...)		\
	do {					\
		if (verbose_mode)		\
			fprintf(stderr, fmt, ## args);	\
	} while (0)

static unsigned int cpu_affinities[NR_CPUS];
static unsigned int next_aff = 0;
static int use_affinity = 0;

pthread_mutex_t affinity_mutex = PTHREAD_MUTEX_INITIALIZER;

static void set_affinity(void)
{
#if HAVE_SCHED_SETAFFINITY
	cpu_set_t mask;
	int cpu, ret;
#endif /* HAVE_SCHED_SETAFFINITY */

	if (!use_affinity)
		return;

#if HAVE_SCHED_SETAFFINITY
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
#if SCHED_SETAFFINITY_ARGS == 2
	sched_setaffinity(0, &mask);
#else
	sched_setaffinity(0, sizeof(mask), &mask);
#endif
#endif /* HAVE_SCHED_SETAFFINITY */
}

/*
 * returns 0 if test should end.
 */
static int test_duration_enqueue(void)
{
	return !test_stop_enqueue;
}

static DEFINE_URCU_TLS(unsigned long long, nr_dequeues);
static DEFINE_URCU_TLS(unsigned long long, nr_enqueues);

static unsigned int nr_dispatchers;
static unsigned int nr_workers;

static struct urcu_workqueue workqueue;

struct test_work {
	struct urcu_work w;
};

static void *thr_dispatcher(void *_count)
{
	unsigned long long *count = _count;
	bool was_nonempty;

	printf_verbose("thread_begin %s, tid %lu\n",
			"dispatcher", urcu_get_thread_id());

	set_affinity();

	while (!test_go)
	{
	}
	cmm_smp_mb();

	for (;;) {
		struct test_work *work = malloc(sizeof(*work));
		enum urcu_enqueue_ret ret;

		if (!work)
			goto fail;
retry:
		printf_verbose("attempt queue work %p\n", work);
		ret = urcu_queue_work(&workqueue, &work->w);
		if (ret == URCU_ENQUEUE_FULL) {
			printf_verbose("queue work %p (queue full)\n", work);
			(void) poll(NULL, 0, 10);
			goto retry;
		}
		printf_verbose("queue work %p (ok)\n", work);
		URCU_TLS(nr_enqueues)++;

		if (caa_unlikely(dispatch_delay_loops))
			loop_sleep(dispatch_delay_loops);
fail:
		if (caa_unlikely(!test_duration_enqueue()))
			break;
	}

	uatomic_inc(&test_enqueue_stopped);
	count[0] = URCU_TLS(nr_enqueues);
	printf_verbose("dispatcher thread_end, tid %lu, "
			"enqueues %llu\n",
			urcu_get_thread_id(),
			URCU_TLS(nr_enqueues));
	return ((void*)1);
}

static void *thr_worker(void *_count)
{
	unsigned long long *count = _count;
	unsigned int counter = 0;
	struct urcu_worker worker;

	printf_verbose("thread_begin %s, tid %lu\n",
			"worker", urcu_get_thread_id());

	set_affinity();

	rcu_register_thread();
	urcu_worker_init(&workqueue, &worker, URCU_WORKER_STEAL);
	//urcu_worker_init(&workqueue, &worker, 0);
	urcu_worker_register(&workqueue, &worker);

	while (!test_go)
	{
	}
	cmm_smp_mb();

	for (;;) {
		enum urcu_accept_ret ret;

		ret = urcu_accept_work(&worker);
		if (ret == URCU_ACCEPT_SHUTDOWN)
			break;
		for (;;) {
			struct urcu_work *work;
			struct test_work *t;

			work = urcu_dequeue_work(&worker);
			if (!work)
				break;
			t = caa_container_of(work, struct test_work, w);
			printf_verbose("dequeue work %p\n", t);
			URCU_TLS(nr_dequeues)++;
			if (caa_unlikely(work_loops))
				loop_sleep(work_loops);
			free(t);
		}
	}
end:
	urcu_worker_unregister(&workqueue, &worker);
	rcu_unregister_thread();

	printf_verbose("worker thread_end, tid %lu, "
			"dequeues %llu\n",
			urcu_get_thread_id(),
			URCU_TLS(nr_dequeues));
	count[0] = URCU_TLS(nr_dequeues);
	return ((void*)2);
}

static void show_usage(int argc, char **argv)
{
	printf("Usage : %s nr_workers nr_dispatchers duration (s) <OPTIONS>\n",
		argv[0]);
	printf("OPTIONS:\n");
	printf("	[-d delay] (dispatcher period (in loops))\n");
	printf("	[-c duration] (worker period (in loops))\n");
	printf("	[-v] (verbose output)\n");
	printf("	[-a cpu#] [-a cpu#]... (affinity)\n");
	printf("	[-w] Wait for worker to empty stack\n");
	printf("	[-m len] (Max queue length. 0 means infinite.))\n");
	printf("\n");
}

int main(int argc, char **argv)
{
	int err;
	pthread_t *tid_dispatcher, *tid_worker;
	void *tret;
	unsigned long long *count_dispatcher, *count_worker;
	unsigned long long tot_enqueues = 0, tot_dequeues = 0;
	unsigned long long end_dequeues = 0;
	int i, a, retval = 0;

	if (argc < 4) {
		show_usage(argc, argv);
		return -1;
	}

	err = sscanf(argv[1], "%u", &nr_workers);
	if (err != 1) {
		show_usage(argc, argv);
		return -1;
	}

	err = sscanf(argv[2], "%u", &nr_dispatchers);
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
		case 'm':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			max_queue_len = atol(argv[++i]);
			break;
		case 'c':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			work_loops = atol(argv[++i]);
			break;
		case 'd':
			if (argc < i + 2) {
				show_usage(argc, argv);
				return -1;
			}
			dispatch_delay_loops = atol(argv[++i]);
			break;
		case 'v':
			verbose_mode = 1;
			break;
		case 'w':
			test_wait_empty = 1;
			break;
		}
	}

	printf_verbose("running test for %lu seconds, %u dispatchers, "
		       "%u workers.\n",
		       duration, nr_dispatchers, nr_workers);
	if (test_wait_empty)
		printf_verbose("Wait for workers to empty workqueue.\n");
	printf_verbose("Work duration: %lu loops.\n", work_loops);
	printf_verbose("Dispatcher arrival delay: %lu loops.\n", dispatch_delay_loops);
	printf_verbose("thread %-6s, tid %lu\n",
			"main", urcu_get_thread_id());

	tid_dispatcher = calloc(nr_dispatchers, sizeof(*tid_dispatcher));
	tid_worker = calloc(nr_workers, sizeof(*tid_worker));
	count_dispatcher = calloc(nr_dispatchers, sizeof(*count_dispatcher));
	count_worker = calloc(nr_workers, sizeof(*count_worker));
	urcu_workqueue_init(&workqueue, max_queue_len);

	next_aff = 0;

	for (i = 0; i < nr_dispatchers; i++) {
		err = pthread_create(&tid_dispatcher[i], NULL, thr_dispatcher,
				     &count_dispatcher[i]);
		if (err != 0)
			exit(1);
	}
	for (i = 0; i < nr_workers; i++) {
		err = pthread_create(&tid_worker[i], NULL, thr_worker,
				     &count_worker[i]);
		if (err != 0)
			exit(1);
	}

	cmm_smp_mb();

	test_go = 1;

	for (i = 0; i < duration; i++) {
		sleep(1);
		if (verbose_mode)
			(void) write(1, ".", 1);
	}

	test_stop_enqueue = 1;
	while (nr_dispatchers != uatomic_read(&test_enqueue_stopped)) {
		sleep(1);
	}

	if (test_wait_empty) {
		while (!cds_wfcq_empty(&workqueue.head, &workqueue.tail)) {
			sleep(1);
		}
	}
	urcu_workqueue_shutdown(&workqueue);

	for (i = 0; i < nr_dispatchers; i++) {
		err = pthread_join(tid_dispatcher[i], &tret);
		if (err != 0)
			exit(1);
		tot_enqueues += count_dispatcher[i];
	}
	for (i = 0; i < nr_workers; i++) {
		err = pthread_join(tid_worker[i], &tret);
		if (err != 0)
			exit(1);
		tot_dequeues += count_worker[i];
	}

	printf("SUMMARY %-25s testdur %4lu nr_dispatchers %3u dispatch_delay_loops %6lu "
		"work_loops %lu nr_workers %3u "
		"nr_enqueues %12llu nr_dequeues %12llu max_queue_len %lu\n",
		argv[0], duration, nr_dispatchers, dispatch_delay_loops, work_loops,
		nr_workers, tot_enqueues, tot_dequeues, max_queue_len);
	free(count_dispatcher);
	free(count_worker);
	free(tid_dispatcher);
	free(tid_worker);
	return retval;
}
