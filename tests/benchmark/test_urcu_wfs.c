/*
 * test_urcu_wfs.c
 *
 * Userspace RCU library - example RCU-based lock-free stack
 *
 * Copyright February 2010 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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
#include <urcu/wfstack.h>

/*
 * External synchronization used.
 */
enum test_sync {
	TEST_SYNC_NONE = 0,
	TEST_SYNC_MUTEX,
};

static enum test_sync test_sync;

static int test_force_sync;

static volatile int test_go, test_stop_enqueue, test_stop_dequeue;

static unsigned long rduration;

static unsigned long duration;

/* read-side C.S. duration, in loops */
static unsigned long wdelay;

static inline void loop_sleep(unsigned long loops)
{
	while (loops-- != 0)
		caa_cpu_relax();
}

static int verbose_mode;

static int test_pop, test_pop_all, test_wait_empty;
static int test_enqueue_stopped;

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
static int test_duration_dequeue(void)
{
	return !test_stop_dequeue;
}

static int test_duration_enqueue(void)
{
	return !test_stop_enqueue;
}

static DEFINE_URCU_TLS(unsigned long long, nr_dequeues);
static DEFINE_URCU_TLS(unsigned long long, nr_enqueues);

static DEFINE_URCU_TLS(unsigned long long, nr_successful_dequeues);
static DEFINE_URCU_TLS(unsigned long long, nr_successful_enqueues);
static DEFINE_URCU_TLS(unsigned long long, nr_empty_dest_enqueues);
static DEFINE_URCU_TLS(unsigned long long, nr_pop_all);
static DEFINE_URCU_TLS(unsigned long long, nr_pop_last);

static unsigned int nr_enqueuers;
static unsigned int nr_dequeuers;

static struct cds_wfs_stack s;

static void *thr_enqueuer(void *_count)
{
	unsigned long long *count = _count;
	bool was_nonempty;

	printf_verbose("thread_begin %s, tid %lu\n",
			"enqueuer", urcu_get_thread_id());

	set_affinity();

	while (!test_go)
	{
	}
	cmm_smp_mb();

	for (;;) {
		struct cds_wfs_node *node = malloc(sizeof(*node));
		if (!node)
			goto fail;
		cds_wfs_node_init(node);
		was_nonempty = cds_wfs_push(&s, node);
		URCU_TLS(nr_successful_enqueues)++;
		if (!was_nonempty)
			URCU_TLS(nr_empty_dest_enqueues)++;

		if (caa_unlikely(wdelay))
			loop_sleep(wdelay);
fail:
		URCU_TLS(nr_enqueues)++;
		if (caa_unlikely(!test_duration_enqueue()))
			break;
	}

	uatomic_inc(&test_enqueue_stopped);
	count[0] = URCU_TLS(nr_enqueues);
	count[1] = URCU_TLS(nr_successful_enqueues);
	count[2] = URCU_TLS(nr_empty_dest_enqueues);
	printf_verbose("enqueuer thread_end, tid %lu, "
			"enqueues %llu successful_enqueues %llu, "
			"empty_dest_enqueues %llu\n",
			urcu_get_thread_id(),
			URCU_TLS(nr_enqueues),
			URCU_TLS(nr_successful_enqueues),
			URCU_TLS(nr_empty_dest_enqueues));
	return ((void*)1);

}

static void do_test_pop(enum test_sync sync)
{
	struct cds_wfs_node *node;
	int state;

	if (sync == TEST_SYNC_MUTEX)
		cds_wfs_pop_lock(&s);
	node = __cds_wfs_pop_with_state_blocking(&s, &state);
	if (sync == TEST_SYNC_MUTEX)
		cds_wfs_pop_unlock(&s);

	if (node) {
		if (state & CDS_WFS_STATE_LAST)
			URCU_TLS(nr_pop_last)++;
		free(node);
		URCU_TLS(nr_successful_dequeues)++;
	}
	URCU_TLS(nr_dequeues)++;
}

static void do_test_pop_all(enum test_sync sync)
{
	struct cds_wfs_head *head;
	struct cds_wfs_node *node, *n;

	if (sync == TEST_SYNC_MUTEX)
		cds_wfs_pop_lock(&s);
	head = __cds_wfs_pop_all(&s);
	if (sync == TEST_SYNC_MUTEX)
		cds_wfs_pop_unlock(&s);

	/* Check if empty */
	if (cds_wfs_first(head) == NULL)
		return;

	URCU_TLS(nr_pop_all)++;
	URCU_TLS(nr_pop_last)++;

	cds_wfs_for_each_blocking_safe(head, node, n) {
		free(node);
		URCU_TLS(nr_successful_dequeues)++;
		URCU_TLS(nr_dequeues)++;
	}
}

static void *thr_dequeuer(void *_count)
{
	unsigned long long *count = _count;
	unsigned int counter = 0;

	printf_verbose("thread_begin %s, tid %lu\n",
			"dequeuer", urcu_get_thread_id());

	set_affinity();

	while (!test_go)
	{
	}
	cmm_smp_mb();

	assert(test_pop || test_pop_all);

	for (;;) {
		if (test_pop && test_pop_all) {
			if (counter & 1)
				do_test_pop(test_sync);
			else
				do_test_pop_all(test_sync);
			counter++;
		} else {
			if (test_pop)
				do_test_pop(test_sync);
			else
				do_test_pop_all(test_sync);
		}

		if (caa_unlikely(!test_duration_dequeue()))
			break;
		if (caa_unlikely(rduration))
			loop_sleep(rduration);
	}

	printf_verbose("dequeuer thread_end, tid %lu, "
			"dequeues %llu, successful_dequeues %llu "
			"pop_all %llu pop_last %llu\n",
			urcu_get_thread_id(),
			URCU_TLS(nr_dequeues), URCU_TLS(nr_successful_dequeues),
			URCU_TLS(nr_pop_all),
			URCU_TLS(nr_pop_last));
	count[0] = URCU_TLS(nr_dequeues);
	count[1] = URCU_TLS(nr_successful_dequeues);
	count[2] = URCU_TLS(nr_pop_all);
	count[3] = URCU_TLS(nr_pop_last);
	return ((void*)2);
}

static void test_end(struct cds_wfs_stack *s, unsigned long long *nr_dequeues,
		unsigned long long *nr_pop_last)
{
	struct cds_wfs_node *node;
	int state;

	do {
		node = cds_wfs_pop_with_state_blocking(s, &state);
		if (node) {
			if (state & CDS_WFS_STATE_LAST)
				(*nr_pop_last)++;
			free(node);
			(*nr_dequeues)++;
		}
	} while (node);
}

static void show_usage(int argc, char **argv)
{
	printf("Usage : %s nr_dequeuers nr_enqueuers duration (s) <OPTIONS>\n",
		argv[0]);
	printf("OPTIONS:\n");
	printf("	[-d delay] (enqueuer period (in loops))\n");
	printf("	[-c duration] (dequeuer period (in loops))\n");
	printf("	[-v] (verbose output)\n");
	printf("	[-a cpu#] [-a cpu#]... (affinity)\n");
	printf("	[-p] (test pop)\n");
	printf("	[-P] (test pop_all, enabled by default)\n");
	printf("	[-M] (use mutex external synchronization)\n");
	printf("		Note: default: no external synchronization used.\n");
	printf("	[-f] (force user-provided synchronization)\n");
	printf("	[-w] Wait for dequeuer to empty stack\n");
	printf("\n");
}

int main(int argc, char **argv)
{
	int err;
	pthread_t *tid_enqueuer, *tid_dequeuer;
	void *tret;
	unsigned long long *count_enqueuer, *count_dequeuer;
	unsigned long long tot_enqueues = 0, tot_dequeues = 0;
	unsigned long long tot_successful_enqueues = 0,
			   tot_successful_dequeues = 0,
			   tot_empty_dest_enqueues = 0,
			   tot_pop_all = 0, tot_pop_last = 0;
	unsigned long long end_dequeues = 0;
	int i, a, retval = 0;

	if (argc < 4) {
		show_usage(argc, argv);
		return -1;
	}

	err = sscanf(argv[1], "%u", &nr_dequeuers);
	if (err != 1) {
		show_usage(argc, argv);
		return -1;
	}

	err = sscanf(argv[2], "%u", &nr_enqueuers);
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
			test_pop = 1;
			break;
		case 'P':
			test_pop_all = 1;
			break;
		case 'M':
			test_sync = TEST_SYNC_MUTEX;
			break;
		case 'w':
			test_wait_empty = 1;
			break;
		case 'f':
			test_force_sync = 1;
			break;
		}
	}

	/* activate pop_all test by default */
	if (!test_pop && !test_pop_all)
		test_pop_all = 1;

	if (test_sync == TEST_SYNC_NONE && nr_dequeuers > 1 && test_pop) {
		if (test_force_sync) {
			fprintf(stderr, "[WARNING] Using pop concurrently "
				"with other pop or pop_all without external "
				"synchronization. Expect run-time failure.\n");
		} else {
			printf("Enforcing mutex synchronization\n");
			test_sync = TEST_SYNC_MUTEX;
		}
	}

	printf_verbose("running test for %lu seconds, %u enqueuers, "
		       "%u dequeuers.\n",
		       duration, nr_enqueuers, nr_dequeuers);
	if (test_pop)
		printf_verbose("pop test activated.\n");
	if (test_pop_all)
		printf_verbose("pop_all test activated.\n");
	if (test_sync == TEST_SYNC_MUTEX)
		printf_verbose("External sync: mutex.\n");
	else
		printf_verbose("External sync: none.\n");
	if (test_wait_empty)
		printf_verbose("Wait for dequeuers to empty stack.\n");
	printf_verbose("Writer delay : %lu loops.\n", rduration);
	printf_verbose("Reader duration : %lu loops.\n", wdelay);
	printf_verbose("thread %-6s, tid %lu\n",
			"main", urcu_get_thread_id());

	tid_enqueuer = calloc(nr_enqueuers, sizeof(*tid_enqueuer));
	tid_dequeuer = calloc(nr_dequeuers, sizeof(*tid_dequeuer));
	count_enqueuer = calloc(nr_enqueuers, 3 * sizeof(*count_enqueuer));
	count_dequeuer = calloc(nr_dequeuers, 4 * sizeof(*count_dequeuer));
	cds_wfs_init(&s);

	next_aff = 0;

	for (i = 0; i < nr_enqueuers; i++) {
		err = pthread_create(&tid_enqueuer[i], NULL, thr_enqueuer,
				     &count_enqueuer[3 * i]);
		if (err != 0)
			exit(1);
	}
	for (i = 0; i < nr_dequeuers; i++) {
		err = pthread_create(&tid_dequeuer[i], NULL, thr_dequeuer,
				     &count_dequeuer[4 * i]);
		if (err != 0)
			exit(1);
	}

	cmm_smp_mb();

	test_go = 1;

	for (i = 0; i < duration; i++) {
		sleep(1);
		if (verbose_mode) {
			fwrite(".", sizeof(char), 1, stdout);
			fflush(stdout);
		}
	}

	test_stop_enqueue = 1;

	if (test_wait_empty) {
		while (nr_enqueuers != uatomic_read(&test_enqueue_stopped)) {
			sleep(1);
		}
		while (!cds_wfs_empty(&s)) {
			sleep(1);
		}
	}

	test_stop_dequeue = 1;

	for (i = 0; i < nr_enqueuers; i++) {
		err = pthread_join(tid_enqueuer[i], &tret);
		if (err != 0)
			exit(1);
		tot_enqueues += count_enqueuer[3 * i];
		tot_successful_enqueues += count_enqueuer[3 * i + 1];
		tot_empty_dest_enqueues += count_enqueuer[3 * i + 2];
	}
	for (i = 0; i < nr_dequeuers; i++) {
		err = pthread_join(tid_dequeuer[i], &tret);
		if (err != 0)
			exit(1);
		tot_dequeues += count_dequeuer[4 * i];
		tot_successful_dequeues += count_dequeuer[4 * i + 1];
		tot_pop_all += count_dequeuer[4 * i + 2];
		tot_pop_last += count_dequeuer[4 * i + 3];
	}
	
	test_end(&s, &end_dequeues, &tot_pop_last);

	printf_verbose("total number of enqueues : %llu, dequeues %llu\n",
		       tot_enqueues, tot_dequeues);
	printf_verbose("total number of successful enqueues : %llu, "
		       "enqueues to empty dest : %llu, "
		       "successful dequeues %llu, "
		       "pop_all : %llu, pop_last : %llu\n",
		       tot_successful_enqueues,
		       tot_empty_dest_enqueues,
		       tot_successful_dequeues,
		       tot_pop_all, tot_pop_last);
	printf("SUMMARY %-25s testdur %4lu nr_enqueuers %3u wdelay %6lu "
		"nr_dequeuers %3u "
		"rdur %6lu nr_enqueues %12llu nr_dequeues %12llu "
		"successful enqueues %12llu enqueues to empty dest %12llu "
		"successful dequeues %12llu pop_all %12llu "
		"pop_last %llu end_dequeues %llu nr_ops %12llu\n",
		argv[0], duration, nr_enqueuers, wdelay,
		nr_dequeuers, rduration, tot_enqueues, tot_dequeues,
		tot_successful_enqueues,
		tot_empty_dest_enqueues,
		tot_successful_dequeues, tot_pop_all, tot_pop_last,
		end_dequeues,
		tot_enqueues + tot_dequeues);
	if (tot_successful_enqueues != tot_successful_dequeues + end_dequeues) {
		printf("WARNING! Discrepancy between nr succ. enqueues %llu vs "
		       "succ. dequeues + end dequeues %llu.\n",
		       tot_successful_enqueues,
		       tot_successful_dequeues + end_dequeues);
		retval = 1;
	}
	/*
	 * The enqueuer should see exactly as many empty queues than the
	 * number of non-empty stacks dequeued.
	 */
	if (tot_empty_dest_enqueues != tot_pop_last) {
		printf("WARNING! Discrepancy between empty enqueue (%llu) and "
			"number of pop last (%llu)\n",
			tot_empty_dest_enqueues,
			tot_pop_last);
		retval = 1;
	}
	cds_wfs_destroy(&s);
	free(count_enqueuer);
	free(count_dequeuer);
	free(tid_enqueuer);
	free(tid_dequeuer);
	return retval;
}
