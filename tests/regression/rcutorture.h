/*
 * rcutorture.h: simple user-level performance/stress test of RCU.
 *
 * Usage:
 * 	./rcu <nreaders> rperf [ <cpustride> ]
 * 		Run a read-side performance test with the specified
 * 		number of readers spaced by <cpustride>.
 * 		Thus "./rcu 16 rperf 2" would run 16 readers on even-numbered
 * 		CPUs from 0 to 30.
 * 	./rcu <nupdaters> uperf [ <cpustride> ]
 * 		Run an update-side performance test with the specified
 * 		number of updaters and specified CPU spacing.
 * 	./rcu <nreaders> perf [ <cpustride> ]
 * 		Run a combined read/update performance test with the specified
 * 		number of readers and one updater and specified CPU spacing.
 * 		The readers run on the low-numbered CPUs and the updater
 * 		of the highest-numbered CPU.
 *
 * The above tests produce output as follows:
 *
 * n_reads: 46008000  n_updates: 146026  nreaders: 2  nupdaters: 1 duration: 1
 * ns/read: 43.4707  ns/update: 6848.1
 *
 * The first line lists the total number of RCU reads and updates executed
 * during the test, the number of reader threads, the number of updater
 * threads, and the duration of the test in seconds.  The second line
 * lists the average duration of each type of operation in nanoseconds,
 * or "nan" if the corresponding type of operation was not performed.
 *
 * 	./rcu <nreaders> stress
 * 		Run a stress test with the specified number of readers and
 * 		one updater.  None of the threads are affinitied to any
 * 		particular CPU.
 *
 * This test produces output as follows:
 *
 * n_reads: 114633217  n_updates: 3903415  n_mberror: 0
 * rcu_stress_count: 114618391 14826 0 0 0 0 0 0 0 0 0
 *
 * The first line lists the number of RCU read and update operations
 * executed, followed by the number of memory-ordering violations
 * (which will be zero in a correct RCU implementation).  The second
 * line lists the number of readers observing progressively more stale
 * data.  A correct RCU implementation will have all but the first two
 * numbers non-zero.
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
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Copyright (c) 2008 Paul E. McKenney, IBM Corporation.
 */

/*
 * Test variables.
 */

#include <stdlib.h>
#include "tap.h"

#define NR_TESTS	1

DEFINE_PER_THREAD(long long, n_reads_pt);
DEFINE_PER_THREAD(long long, n_updates_pt);

enum callrcu_type {
	CALLRCU_GLOBAL,
	CALLRCU_PERCPU,
	CALLRCU_PERTHREAD,
};

enum writer_state {
	WRITER_STATE_SYNC_RCU,
	WRITER_STATE_CALL_RCU,
	WRITER_STATE_POLL_RCU,
};

static enum callrcu_type callrcu_type = CALLRCU_GLOBAL;

long long n_reads = 0LL;
long n_updates = 0L;
int nthreadsrunning;
char argsbuf[64];

#define GOFLAG_INIT 0
#define GOFLAG_RUN  1
#define GOFLAG_STOP 2

volatile int goflag __attribute__((__aligned__(CAA_CACHE_LINE_SIZE)))
        = GOFLAG_INIT;

#define RCU_READ_RUN 1000

//MD
#define RCU_READ_NESTABLE

#ifdef RCU_READ_NESTABLE
#define rcu_read_lock_nest() rcu_read_lock()
#define rcu_read_unlock_nest() rcu_read_unlock()
#else /* #ifdef RCU_READ_NESTABLE */
#define rcu_read_lock_nest()
#define rcu_read_unlock_nest()
#endif /* #else #ifdef RCU_READ_NESTABLE */

#ifdef TORTURE_QSBR
#define mark_rcu_quiescent_state	rcu_quiescent_state
#define put_thread_offline		rcu_thread_offline
#define put_thread_online		rcu_thread_online
#endif

#ifndef mark_rcu_quiescent_state
#define mark_rcu_quiescent_state() do {} while (0)
#endif /* #ifdef mark_rcu_quiescent_state */

#ifndef put_thread_offline
#define put_thread_offline()		do {} while (0)
#define put_thread_online()		do {} while (0)
#define put_thread_online_delay()	do {} while (0)
#else /* #ifndef put_thread_offline */
#define put_thread_online_delay()	synchronize_rcu()
#endif /* #else #ifndef put_thread_offline */

/*
 * Performance test.
 */

static
void *rcu_read_perf_test(void *arg)
{
	int i;
	int me = (long)arg;
	long long n_reads_local = 0;

	rcu_register_thread();
	run_on(me);
	uatomic_inc(&nthreadsrunning);
	put_thread_offline();
	while (goflag == GOFLAG_INIT)
		(void) poll(NULL, 0, 1);
	put_thread_online();
	while (goflag == GOFLAG_RUN) {
		for (i = 0; i < RCU_READ_RUN; i++) {
			rcu_read_lock();
			/* rcu_read_lock_nest(); */
			/* rcu_read_unlock_nest(); */
			rcu_read_unlock();
		}
		n_reads_local += RCU_READ_RUN;
		mark_rcu_quiescent_state();
	}
	__get_thread_var(n_reads_pt) += n_reads_local;
	put_thread_offline();
	rcu_unregister_thread();

	return (NULL);
}

static
void *rcu_update_perf_test(void *arg __attribute__((unused)))
{
	long long n_updates_local = 0;

	if (callrcu_type == CALLRCU_PERTHREAD) {
		struct call_rcu_data *crdp;

		crdp = create_call_rcu_data(0, -1);
		if (crdp != NULL) {
			diag("Successfully using per-thread call_rcu() worker.");
			set_thread_call_rcu_data(crdp);
		}
	}
	uatomic_inc(&nthreadsrunning);
	while (goflag == GOFLAG_INIT)
		(void) poll(NULL, 0, 1);
	while (goflag == GOFLAG_RUN) {
		synchronize_rcu();
		n_updates_local++;
	}
	__get_thread_var(n_updates_pt) += n_updates_local;
	if (callrcu_type == CALLRCU_PERTHREAD) {
		struct call_rcu_data *crdp;

		crdp = get_thread_call_rcu_data();
		set_thread_call_rcu_data(NULL);
		call_rcu_data_free(crdp);
	}
	return NULL;
}

static
void perftestinit(void)
{
	init_per_thread(n_reads_pt, 0LL);
	init_per_thread(n_updates_pt, 0LL);
	uatomic_set(&nthreadsrunning, 0);
}

static
int perftestrun(int nthreads, int nreaders, int nupdaters)
{
	int t;
	int duration = 1;

	cmm_smp_mb();
	while (uatomic_read(&nthreadsrunning) < nthreads)
		(void) poll(NULL, 0, 1);
	goflag = GOFLAG_RUN;
	cmm_smp_mb();
	sleep(duration);
	cmm_smp_mb();
	goflag = GOFLAG_STOP;
	cmm_smp_mb();
	wait_all_threads();
	for_each_thread(t) {
		n_reads += per_thread(n_reads_pt, t);
		n_updates += per_thread(n_updates_pt, t);
	}
	diag("n_reads: %lld  n_updates: %ld  nreaders: %d  nupdaters: %d duration: %d",
	       n_reads, n_updates, nreaders, nupdaters, duration);
	diag("ns/read: %g  ns/update: %g",
	       ((duration * 1000*1000*1000.*(double)nreaders) /
	        (double)n_reads),
	       ((duration * 1000*1000*1000.*(double)nupdaters) /
	        (double)n_updates));
	if (get_cpu_call_rcu_data(0)) {
		diag("Deallocating per-CPU call_rcu threads.\n");
		free_all_cpu_call_rcu_data();
	}
	return 0;
}

static
int perftest(int nreaders, int cpustride)
{
	int i;
	long arg;

	perftestinit();
	for (i = 0; i < nreaders; i++) {
		arg = (long)(i * cpustride);
		create_thread(rcu_read_perf_test, (void *)arg);
	}
	arg = (long)(i * cpustride);
	create_thread(rcu_update_perf_test, (void *)arg);
	return perftestrun(i + 1, nreaders, 1);
}

static
int rperftest(int nreaders, int cpustride)
{
	int i;
	long arg;

	perftestinit();
	init_per_thread(n_reads_pt, 0LL);
	for (i = 0; i < nreaders; i++) {
		arg = (long)(i * cpustride);
		create_thread(rcu_read_perf_test, (void *)arg);
	}
	return perftestrun(i, nreaders, 0);
}

static
int uperftest(int nupdaters, int cpustride)
{
	int i;
	long arg;

	perftestinit();
	init_per_thread(n_reads_pt, 0LL);
	for (i = 0; i < nupdaters; i++) {
		arg = (long)(i * cpustride);
		create_thread(rcu_update_perf_test, (void *)arg);
	}
	return perftestrun(i, 0, nupdaters);
}

/*
 * Stress test.
 */

#define RCU_STRESS_PIPE_LEN 10

struct rcu_stress {
	int pipe_count;
	int mbtest;
};

struct rcu_stress rcu_stress_array[RCU_STRESS_PIPE_LEN] = { { 0, 0 } };
struct rcu_stress *rcu_stress_current;
int rcu_stress_idx = 0;

int n_mberror = 0;
DEFINE_PER_THREAD(long long [RCU_STRESS_PIPE_LEN + 1], rcu_stress_count);

int garbage = 0;

static
void *rcu_read_stress_test(void *arg __attribute__((unused)))
{
	int i;
	int itercnt = 0;
	struct rcu_stress *p;
	int pc;

	rcu_register_thread();
	put_thread_offline();
	while (goflag == GOFLAG_INIT)
		(void) poll(NULL, 0, 1);
	put_thread_online();
	while (goflag == GOFLAG_RUN) {
		rcu_read_lock();
		p = rcu_dereference(rcu_stress_current);
		if (p->mbtest == 0)
			n_mberror++;
		rcu_read_lock_nest();
		for (i = 0; i < 100; i++)
			garbage++;
		rcu_read_unlock_nest();
		pc = p->pipe_count;
		rcu_read_unlock();
		if ((pc > RCU_STRESS_PIPE_LEN) || (pc < 0))
			pc = RCU_STRESS_PIPE_LEN;
		__get_thread_var(rcu_stress_count)[pc]++;
		__get_thread_var(n_reads_pt)++;
		mark_rcu_quiescent_state();
		if ((++itercnt % 0x1000) == 0) {
			put_thread_offline();
			put_thread_online_delay();
			put_thread_online();
		}
	}
	put_thread_offline();
	rcu_unregister_thread();

	return (NULL);
}

static pthread_mutex_t call_rcu_test_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t call_rcu_test_cond = PTHREAD_COND_INITIALIZER;
static bool call_rcu_wait;

static
void rcu_update_stress_test_rcu(struct rcu_head *head __attribute__((unused)))
{
	int ret;

	ret = pthread_mutex_lock(&call_rcu_test_mutex);
	if (ret) {
		errno = ret;
		diag("pthread_mutex_lock: %s",
			strerror(errno));
		abort();
	}
	ret = pthread_cond_signal(&call_rcu_test_cond);
	if (ret) {
		errno = ret;
		diag("pthread_cond_signal: %s",
			strerror(errno));
		abort();
	}
	call_rcu_wait = false;
	ret = pthread_mutex_unlock(&call_rcu_test_mutex);
	if (ret) {
		errno = ret;
		diag("pthread_mutex_unlock: %s",
			strerror(errno));
		abort();
	}
}

static
void advance_writer_state(enum writer_state *state)
{
	switch (*state) {
	case WRITER_STATE_SYNC_RCU:
		*state = WRITER_STATE_CALL_RCU;
		break;
	case WRITER_STATE_CALL_RCU:
		*state = WRITER_STATE_POLL_RCU;
		break;
	case WRITER_STATE_POLL_RCU:
		*state = WRITER_STATE_SYNC_RCU;
		break;
	}
}

static
void *rcu_update_stress_test(void *arg __attribute__((unused)))
{
	int i;
	struct rcu_stress *p;
	struct rcu_head rh;
	enum writer_state writer_state = WRITER_STATE_SYNC_RCU;

	while (goflag == GOFLAG_INIT)
		(void) poll(NULL, 0, 1);
	while (goflag == GOFLAG_RUN) {
		i = rcu_stress_idx + 1;
		if (i >= RCU_STRESS_PIPE_LEN)
			i = 0;
		p = &rcu_stress_array[i];
		p->mbtest = 0;
		cmm_smp_mb();
		p->pipe_count = 0;
		p->mbtest = 1;
		rcu_assign_pointer(rcu_stress_current, p);
		rcu_stress_idx = i;
		for (i = 0; i < RCU_STRESS_PIPE_LEN; i++)
			if (i != rcu_stress_idx)
				rcu_stress_array[i].pipe_count++;
		switch (writer_state) {
		case WRITER_STATE_SYNC_RCU:
			synchronize_rcu();
			break;
		case WRITER_STATE_CALL_RCU:
		{
			int ret;

			ret = pthread_mutex_lock(&call_rcu_test_mutex);
			if (ret) {
				errno = ret;
				diag("pthread_mutex_lock: %s",
					strerror(errno));
				abort();
			}
			rcu_register_thread();
			call_rcu(&rh, rcu_update_stress_test_rcu);
			rcu_unregister_thread();
			/*
			 * Our MacOS X test machine with the following
			 * config:
			 * 15.6.0 Darwin Kernel Version 15.6.0
			 * root:xnu-3248.60.10~1/RELEASE_X86_64
			 * appears to have issues with liburcu-signal
			 * signal being delivered on top of
			 * pthread_cond_wait. It seems to make the
			 * thread continue, and therefore corrupt the
			 * rcu_head. Work around this issue by
			 * unregistering the RCU read-side thread
			 * immediately after call_rcu (call_rcu needs
			 * us to be registered RCU readers).
			 */
			call_rcu_wait = true;
			do {
				ret = pthread_cond_wait(&call_rcu_test_cond,
							&call_rcu_test_mutex);
			} while (call_rcu_wait);
			if (ret) {
				errno = ret;
				diag("pthread_cond_signal: %s",
					strerror(errno));
				abort();
			}
			ret = pthread_mutex_unlock(&call_rcu_test_mutex);
			if (ret) {
				errno = ret;
				diag("pthread_mutex_unlock: %s",
					strerror(errno));
				abort();
			}
			break;
		}
		case WRITER_STATE_POLL_RCU:
		{
			struct urcu_gp_poll_state poll_state;

			rcu_register_thread();
			poll_state = start_poll_synchronize_rcu();
			rcu_unregister_thread();
			while (!poll_state_synchronize_rcu(poll_state))
				(void) poll(NULL, 0, 1);	/* Wait for 1ms */
			break;
		}
		}
		n_updates++;
		advance_writer_state(&writer_state);
	}

	return NULL;
}

static
void *rcu_fake_update_stress_test(void *arg __attribute__((unused)))
{
	if (callrcu_type == CALLRCU_PERTHREAD) {
		struct call_rcu_data *crdp;

		crdp = create_call_rcu_data(0, -1);
		if (crdp != NULL) {
			diag("Successfully using per-thread call_rcu() worker.");
			set_thread_call_rcu_data(crdp);
		}
	}
	while (goflag == GOFLAG_INIT)
		(void) poll(NULL, 0, 1);
	while (goflag == GOFLAG_RUN) {
		synchronize_rcu();
		(void) poll(NULL, 0, 1);
	}
	if (callrcu_type == CALLRCU_PERTHREAD) {
		struct call_rcu_data *crdp;

		crdp = get_thread_call_rcu_data();
		set_thread_call_rcu_data(NULL);
		call_rcu_data_free(crdp);
	}
	return NULL;
}

static
int stresstest(int nreaders)
{
	int i;
	int t;
	long long *p;
	long long sum;

	init_per_thread(n_reads_pt, 0LL);
	for_each_thread(t) {
		p = &per_thread(rcu_stress_count,t)[0];
		for (i = 0; i <= RCU_STRESS_PIPE_LEN; i++)
			p[i] = 0LL;
	}
	rcu_stress_current = &rcu_stress_array[0];
	rcu_stress_current->pipe_count = 0;
	rcu_stress_current->mbtest = 1;
	for (i = 0; i < nreaders; i++)
		create_thread(rcu_read_stress_test, NULL);
	create_thread(rcu_update_stress_test, NULL);
	for (i = 0; i < 5; i++)
		create_thread(rcu_fake_update_stress_test, NULL);
	cmm_smp_mb();
	goflag = GOFLAG_RUN;
	cmm_smp_mb();
	sleep(10);
	cmm_smp_mb();
	goflag = GOFLAG_STOP;
	cmm_smp_mb();
	wait_all_threads();
	for_each_thread(t)
		n_reads += per_thread(n_reads_pt, t);
	diag("n_reads: %lld  n_updates: %ld  n_mberror: %d",
	       n_reads, n_updates, n_mberror);
	rdiag_start();
	rdiag("rcu_stress_count:");
	for (i = 0; i <= RCU_STRESS_PIPE_LEN; i++) {
		sum = 0LL;
		for_each_thread(t) {
			sum += per_thread(rcu_stress_count, t)[i];
		}
		rdiag(" %lld", sum);
	}
	rdiag_end();
	if (get_cpu_call_rcu_data(0)) {
		diag("Deallocating per-CPU call_rcu threads.");
		free_all_cpu_call_rcu_data();
	}
	if (!n_mberror)
		return 0;
	else
		return -1;
}

/*
 * Mainprogram.
 */

static
void usage(char *argv[]) __attribute__((__noreturn__));

static
void usage(char *argv[])
{
	diag("Usage: %s nreaders [ perf | rperf | uperf | stress ] [ stride ] [ callrcu_global | callrcu_percpu | callrcu_perthread ]\n", argv[0]);
	exit(-1);
}

int main(int argc, char *argv[])
{
	int nreaders = 1;
	int cpustride = 1;

	plan_tests(NR_TESTS);

	smp_init();
	//rcu_init();
	if (argc > 4) {
		const char *callrcu_str = argv[4];;

		if (strcmp(callrcu_str, "callrcu_global") == 0) {
			callrcu_type = CALLRCU_GLOBAL;
		} else if (strcmp(callrcu_str, "callrcu_percpu") == 0) {
			callrcu_type = CALLRCU_PERCPU;
		} else if (strcmp(callrcu_str, "callrcu_perthread") == 0) {
			callrcu_type = CALLRCU_PERTHREAD;
		} else {
			usage(argv);
			goto end;
		}
	}

	switch (callrcu_type) {
	case CALLRCU_GLOBAL:
		diag("Using global per-process call_rcu thread.");
		break;
	case CALLRCU_PERCPU:
		diag("Using per-CPU call_rcu threads.");
		if (create_all_cpu_call_rcu_data(0))
			diag("create_all_cpu_call_rcu_data: %s",
				strerror(errno));
		break;
	case CALLRCU_PERTHREAD:
		diag("Using per-thread call_rcu() worker.");
		break;
	default:
		abort();
	}

#ifdef DEBUG_YIELD
	yield_active |= YIELD_READ;
	yield_active |= YIELD_WRITE;
#endif

	if (argc > 1) {
		if (strcmp(argv[1], "-h") == 0
				|| strcmp(argv[1], "--help") == 0) {
			usage(argv);
			goto end;
		}
		nreaders = strtoul(argv[1], NULL, 0);
		if (argc == 2) {
			ok(!perftest(nreaders, cpustride),
				"perftest readers: %d, stride: %d",
				nreaders, cpustride);
			goto end;
		}
		if (argc > 3)
			cpustride = strtoul(argv[3], NULL, 0);
		if (strcmp(argv[2], "perf") == 0)
			ok(!perftest(nreaders, cpustride),
				"perftest readers: %d, stride: %d",
				nreaders, cpustride);
		else if (strcmp(argv[2], "rperf") == 0)
			ok(!rperftest(nreaders, cpustride),
				"rperftest readers: %d, stride: %d",
				nreaders, cpustride);
		else if (strcmp(argv[2], "uperf") == 0)
			ok(!uperftest(nreaders, cpustride),
				"uperftest readers: %d, stride: %d",
				nreaders, cpustride);
		else if (strcmp(argv[2], "stress") == 0)
			ok(!stresstest(nreaders),
				"stresstest readers: %d, stride: %d",
				nreaders, cpustride);
		else
			usage(argv);
	} else {
		usage(argv);
	}
end:
	return exit_status();
}
