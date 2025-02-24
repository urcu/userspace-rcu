// SPDX-FileCopyrightText: 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
//
// SPDX-License-Identifier: GPL-2.0-or-later

/*
 * Userspace RCU library - test program (with batch reclamation)
 */

#include <stdio.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdio.h>
#include <errno.h>

#include <urcu/arch.h>
#include <urcu/assert.h>
#include <urcu/tls-compat.h>
#include <urcu/uatomic.h>
#include "thread-id.h"
#include "../common/debug-yield.h"

/* hardcoded number of CPUs */
#define NR_CPUS 16384

#ifndef DYNAMIC_LINK_TEST
#define _LGPL_SOURCE
#endif
#include <urcu.h>

struct test_array {
	int a;
};

static unsigned long wdelay;

static struct test_array *test_rcu_pointer;

static long reclaim_batch = 1;

struct reclaim_queue {
	void **queue;	/* Beginning of queue */
	void **head;	/* Insert position */
};

static struct reclaim_queue *pending_reclaims;

static unsigned long duration;

/* read-side C.S. duration, in loops */
static unsigned long rduration;

/* write-side C.S. duration, in loops */
static unsigned long wduration;

static inline void loop_sleep(unsigned long loops)
{
	while (loops-- != 0)
		caa_cpu_relax();
}

static int verbose_mode;

#define printf_verbose(fmt, args...)		\
	do {					\
		if (verbose_mode)		\
			printf(fmt, args);	\
	} while (0)

static unsigned int cpu_affinities[NR_CPUS];
static unsigned int next_aff = 0;
static int use_affinity = 0;

pthread_mutex_t affinity_mutex = PTHREAD_MUTEX_INITIALIZER;

static void set_affinity(void)
{
#ifdef HAVE_SCHED_SETAFFINITY
	cpu_set_t mask;
	int cpu, ret;
#endif /* HAVE_SCHED_SETAFFINITY */

	if (!use_affinity)
		return;

#ifdef HAVE_SCHED_SETAFFINITY
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
#endif /* HAVE_SCHED_SETAFFINITY */
}

static DEFINE_URCU_TLS(unsigned long long, nr_writes);
static DEFINE_URCU_TLS(unsigned long long, nr_reads);

static
unsigned long long __attribute__((__aligned__(CAA_CACHE_LINE_SIZE))) *tot_nr_writes;

static unsigned int nr_readers;
static unsigned int nr_writers;

pthread_mutex_t rcu_copy_mutex = PTHREAD_MUTEX_INITIALIZER;

static
void *thr_reader(void *_count)
{
	unsigned long long *count = _count;
	struct test_array *local_ptr;

	printf_verbose("thread_begin %s, tid %lu\n",
			"reader", urcu_get_thread_id());

	set_affinity();

	rcu_register_thread();

	wait_until_go();

	for (;;) {
		rcu_read_lock();
		local_ptr = rcu_dereference(test_rcu_pointer);
		rcu_debug_yield_read();
		if (local_ptr)
			urcu_posix_assert(local_ptr->a == 8);
		if (caa_unlikely(rduration))
			loop_sleep(rduration);
		rcu_read_unlock();
		URCU_TLS(nr_reads)++;
		if (caa_unlikely(!test_duration_read()))
			break;
	}

	rcu_unregister_thread();

	*count = URCU_TLS(nr_reads);
	printf_verbose("thread_end %s, tid %lu\n",
			"reader", urcu_get_thread_id());
	return ((void*)1);

}

static void rcu_gc_clear_queue(unsigned long wtidx)
{
	void **p;

	/* Wait for Q.S and empty queue */
	synchronize_rcu();

	for (p = pending_reclaims[wtidx].queue;
			p < pending_reclaims[wtidx].head; p++) {
		/* poison */
		if (*p)
			((struct test_array *)*p)->a = 0;
		free(*p);
	}
	pending_reclaims[wtidx].head = pending_reclaims[wtidx].queue;
}

/* Using per-thread queue */
static void rcu_gc_reclaim(unsigned long wtidx, void *old)
{
	/* Queue pointer */
	*pending_reclaims[wtidx].head = old;
	pending_reclaims[wtidx].head++;

	if (caa_likely(pending_reclaims[wtidx].head - pending_reclaims[wtidx].queue
			< reclaim_batch))
		return;

	rcu_gc_clear_queue(wtidx);
}

static
void *thr_writer(void *data)
{
	unsigned long wtidx = (unsigned long)data;
#ifdef TEST_LOCAL_GC
	struct test_array *old = NULL;
#else
	struct test_array *new, *old;
#endif

	printf_verbose("thread_begin %s, tid %lu\n",
			"writer", urcu_get_thread_id());

	set_affinity();

	wait_until_go();

	for (;;) {
#ifndef TEST_LOCAL_GC
		new = malloc(sizeof(*new));
		new->a = 8;
		old = rcu_xchg_pointer(&test_rcu_pointer, new);
#endif
		if (caa_unlikely(wduration))
			loop_sleep(wduration);
		rcu_gc_reclaim(wtidx, old);
		URCU_TLS(nr_writes)++;
		if (caa_unlikely(!test_duration_write()))
			break;
		if (caa_unlikely(wdelay))
			loop_sleep(wdelay);
	}

	printf_verbose("thread_end %s, tid %lu\n",
			"writer", urcu_get_thread_id());
	tot_nr_writes[wtidx] = URCU_TLS(nr_writes);
	return ((void*)2);
}

static
void show_usage(char **argv)
{
	printf("Usage : %s nr_readers nr_writers duration (s) <OPTIONS>\n",
		argv[0]);
	printf("OPTIONS:\n");
	printf("	[-r] [-w] (yield reader and/or writer)\n");
	printf("	[-d delay] (writer period (us))\n");
	printf("	[-c duration] (reader C.S. duration (in loops))\n");
	printf("	[-e duration] (writer C.S. duration (in loops))\n");
	printf("	[-v] (verbose output)\n");
	printf("	[-a cpu#] [-a cpu#]... (affinity)\n");
	printf("\n");
}

int main(int argc, char **argv)
{
	int err;
	pthread_t *tid_reader, *tid_writer;
	void *tret;
	unsigned long long *count_reader;
	unsigned long long tot_reads = 0, tot_writes = 0;
	int i, a;
	unsigned int i_thr;

	if (argc < 4) {
		show_usage(argv);
		return -1;
	}

	err = sscanf(argv[1], "%u", &nr_readers);
	if (err != 1) {
		show_usage(argv);
		return -1;
	}

	err = sscanf(argv[2], "%u", &nr_writers);
	if (err != 1) {
		show_usage(argv);
		return -1;
	}

	err = sscanf(argv[3], "%lu", &duration);
	if (err != 1) {
		show_usage(argv);
		return -1;
	}

	for (i = 4; i < argc; i++) {
		if (argv[i][0] != '-')
			continue;
		switch (argv[i][1]) {
		case 'r':
			rcu_debug_yield_enable(RCU_YIELD_READ);
			break;
		case 'w':
			rcu_debug_yield_enable(RCU_YIELD_WRITE);
			break;
		case 'a':
			if (argc < i + 2) {
				show_usage(argv);
				return -1;
			}
			a = atoi(argv[++i]);
			cpu_affinities[next_aff++] = a;
			use_affinity = 1;
			printf_verbose("Adding CPU %d affinity\n", a);
			break;
		case 'b':
			if (argc < i + 2) {
				show_usage(argv);
				return -1;
			}
			reclaim_batch = atol(argv[++i]);
			break;
		case 'c':
			if (argc < i + 2) {
				show_usage(argv);
				return -1;
			}
			rduration = atol(argv[++i]);
			break;
		case 'd':
			if (argc < i + 2) {
				show_usage(argv);
				return -1;
			}
			wdelay = atol(argv[++i]);
			break;
		case 'e':
			if (argc < i + 2) {
				show_usage(argv);
				return -1;
			}
			wduration = atol(argv[++i]);
			break;
		case 'v':
			verbose_mode = 1;
			break;
		}
	}

	printf_verbose("running test for %lu seconds, %u readers, %u writers.\n",
		duration, nr_readers, nr_writers);
	printf_verbose("Writer delay : %lu loops.\n", wdelay);
	printf_verbose("Reader duration : %lu loops.\n", rduration);
	printf_verbose("thread %-6s, tid %lu\n",
			"main", urcu_get_thread_id());

	tid_reader = calloc(nr_readers, sizeof(*tid_reader));
	tid_writer = calloc(nr_writers, sizeof(*tid_writer));
	count_reader = calloc(nr_readers, sizeof(*count_reader));
	tot_nr_writes = calloc(nr_writers, sizeof(*tot_nr_writes));
	pending_reclaims = calloc(nr_writers, sizeof(*pending_reclaims));

	if (reclaim_batch * sizeof(*pending_reclaims[0].queue)
			< CAA_CACHE_LINE_SIZE)
		for (i_thr = 0; i_thr < nr_writers; i_thr++)
			pending_reclaims[i_thr].queue = calloc(1, CAA_CACHE_LINE_SIZE);
	else
		for (i_thr = 0; i_thr < nr_writers; i_thr++)
			pending_reclaims[i_thr].queue = calloc(reclaim_batch,
					sizeof(*pending_reclaims[i_thr].queue));
	for (i_thr = 0; i_thr < nr_writers; i_thr++)
		pending_reclaims[i_thr].head = pending_reclaims[i_thr].queue;

	next_aff = 0;

	for (i_thr = 0; i_thr < nr_readers; i_thr++) {
		err = pthread_create(&tid_reader[i_thr], NULL, thr_reader,
				     &count_reader[i_thr]);
		if (err != 0)
			exit(1);
	}
	for (i_thr = 0; i_thr < nr_writers; i_thr++) {
		err = pthread_create(&tid_writer[i_thr], NULL, thr_writer,
				     (void *)(long)i_thr);
		if (err != 0)
			exit(1);
	}

	test_for(duration);

	for (i_thr = 0; i_thr < nr_readers; i_thr++) {
		err = pthread_join(tid_reader[i_thr], &tret);
		if (err != 0)
			exit(1);
		tot_reads += count_reader[i_thr];
	}
	for (i_thr = 0; i_thr < nr_writers; i_thr++) {
		err = pthread_join(tid_writer[i_thr], &tret);
		if (err != 0)
			exit(1);
		tot_writes += tot_nr_writes[i_thr];
		rcu_gc_clear_queue(i_thr);
	}

	printf_verbose("total number of reads : %llu, writes %llu\n", tot_reads,
	       tot_writes);
	printf("SUMMARY %-25s testdur %4lu nr_readers %3u rdur %6lu wdur %6lu "
		"nr_writers %3u "
		"wdelay %6lu nr_reads %12llu nr_writes %12llu nr_ops %12llu "
		"batch %ld\n",
		argv[0], duration, nr_readers, rduration, wduration,
		nr_writers, wdelay, tot_reads, tot_writes,
		tot_reads + tot_writes, reclaim_batch);

	free(tid_reader);
	free(tid_writer);
	free(count_reader);
	free(tot_nr_writes);

	for (i_thr = 0; i_thr < nr_writers; i_thr++)
		free(pending_reclaims[i_thr].queue);
	free(pending_reclaims);

	return 0;
}
