/*
 * urcu.c
 *
 * Userspace RCU library
 *
 * Copyright February 2009 - Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
 *
 * Distributed under GPLv2
 */

#include <stdio.h>
#include <pthread.h>
#include <signal.h>
#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "urcu.h"

pthread_mutex_t urcu_mutex = PTHREAD_MUTEX_INITIALIZER;

/*
 * Global grace period counter.
 * Contains the current RCU_GP_CTR_BIT.
 * Also has a RCU_GP_CTR_BIT of 1, to accelerate the reader fast path.
 */
long urcu_gp_ctr = RCU_GP_COUNT;

long __thread urcu_active_readers;

/* Thread IDs of registered readers */
#define INIT_NUM_THREADS 4

struct reader_data {
	pthread_t tid;
	long *urcu_active_readers;
};

#ifdef DEBUG_YIELD
unsigned int yield_active;
unsigned int __thread rand_yield;
#endif

static struct reader_data *reader_data;
static int num_readers, alloc_readers;
#ifndef DEBUG_FULL_MB
static int sig_done;
#endif

void internal_urcu_lock(void)
{
	int ret;
	ret = pthread_mutex_lock(&urcu_mutex);
	if (ret) {
		perror("Error in pthread mutex lock");
		exit(-1);
	}
}

void internal_urcu_unlock(void)
{
	int ret;

	ret = pthread_mutex_unlock(&urcu_mutex);
	if (ret) {
		perror("Error in pthread mutex unlock");
		exit(-1);
	}
}

/*
 * called with urcu_mutex held.
 */
static void switch_next_urcu_qparity(void)
{
	urcu_gp_ctr ^= RCU_GP_CTR_BIT;
}

#ifdef DEBUG_FULL_MB
static void force_mb_single_thread(pthread_t tid)
{
	smp_mb();
}

static void force_mb_all_threads(void)
{
	smp_mb();
}
#else

static void force_mb_single_thread(pthread_t tid)
{
	assert(reader_data);
	sig_done = 0;
	/*
	 * pthread_kill has a smp_mb(). But beware, we assume it performs
	 * a cache flush on architectures with non-coherent cache. Let's play
	 * safe and don't assume anything : we use smp_mc() to make sure the
	 * cache flush is enforced.
	 * smp_mb();    write sig_done before sending the signals
	 */
	smp_mc();	/* write sig_done before sending the signals */
	pthread_kill(tid, SIGURCU);
	/*
	 * Wait for sighandler (and thus mb()) to execute on every thread.
	 * BUSY-LOOP.
	 */
	while (LOAD_SHARED(sig_done) < 1)
		cpu_relax();
	smp_mb();	/* read sig_done before ending the barrier */
}

static void force_mb_all_threads(void)
{
	struct reader_data *index;
	/*
	 * Ask for each threads to execute a smp_mb() so we can consider the
	 * compiler barriers around rcu read lock as real memory barriers.
	 */
	if (!reader_data)
		return;
	sig_done = 0;
	/*
	 * pthread_kill has a smp_mb(). But beware, we assume it performs
	 * a cache flush on architectures with non-coherent cache. Let's play
	 * safe and don't assume anything : we use smp_mc() to make sure the
	 * cache flush is enforced.
	 * smp_mb();    write sig_done before sending the signals
	 */
	smp_mc();	/* write sig_done before sending the signals */
	for (index = reader_data; index < reader_data + num_readers; index++)
		pthread_kill(index->tid, SIGURCU);
	/*
	 * Wait for sighandler (and thus mb()) to execute on every thread.
	 * BUSY-LOOP.
	 */
	while (LOAD_SHARED(sig_done) < num_readers)
		cpu_relax();
	smp_mb();	/* read sig_done before ending the barrier */
}
#endif

void wait_for_quiescent_state(void)
{
	struct reader_data *index;

	if (!reader_data)
		return;
	/*
	 * Wait for each thread urcu_active_readers count to become 0.
	 */
	for (index = reader_data; index < reader_data + num_readers; index++) {
		int wait_loops = 0;
		/*
		 * BUSY-LOOP. Force the reader thread to commit its
		 * urcu_active_readers update to memory if we wait for too long.
		 */
		while (rcu_old_gp_ongoing(index->urcu_active_readers)) {
			if (wait_loops++ == KICK_READER_LOOPS) {
				force_mb_single_thread(index->tid);
				wait_loops = 0;
			} else {
				cpu_relax();
			}
		}
	}
}

void synchronize_rcu(void)
{
	internal_urcu_lock();

	/* All threads should read qparity before accessing data structure
	 * where new ptr points to. Must be done within internal_urcu_lock
	 * because it iterates on reader threads.*/
	/* Write new ptr before changing the qparity */
	force_mb_all_threads();

	switch_next_urcu_qparity();	/* 0 -> 1 */

	/*
	 * Must commit qparity update to memory before waiting for parity
	 * 0 quiescent state. Failure to do so could result in the writer
	 * waiting forever while new readers are always accessing data (no
	 * progress).
	 */
	smp_mc();

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	wait_for_quiescent_state();	/* Wait readers in parity 0 */

	/*
	 * Must finish waiting for quiescent state for parity 0 before
	 * committing qparity update to memory. Failure to do so could result in
	 * the writer waiting forever while new readers are always accessing
	 * data (no progress).
	 */
	smp_mc();

	switch_next_urcu_qparity();	/* 1 -> 0 */

	/*
	 * Must commit qparity update to memory before waiting for parity
	 * 1 quiescent state. Failure to do so could result in the writer
	 * waiting forever while new readers are always accessing data (no
	 * progress).
	 */
	smp_mc();

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	wait_for_quiescent_state();	/* Wait readers in parity 1 */

	/* Finish waiting for reader threads before letting the old ptr being
	 * freed. Must be done within internal_urcu_lock because it iterates on
	 * reader threads. */
	force_mb_all_threads();

	internal_urcu_unlock();
}

void urcu_add_reader(pthread_t id)
{
	struct reader_data *oldarray;

	if (!reader_data) {
		alloc_readers = INIT_NUM_THREADS;
		num_readers = 0;
		reader_data =
			malloc(sizeof(struct reader_data) * alloc_readers);
	}
	if (alloc_readers < num_readers + 1) {
		oldarray = reader_data;
		reader_data = malloc(sizeof(struct reader_data)
				* (alloc_readers << 1));
		memcpy(reader_data, oldarray,
			sizeof(struct reader_data) * alloc_readers);
		alloc_readers <<= 1;
		free(oldarray);
	}
	reader_data[num_readers].tid = id;
	/* reference to the TLS of _this_ reader thread. */
	reader_data[num_readers].urcu_active_readers = &urcu_active_readers;
	num_readers++;
}

/*
 * Never shrink (implementation limitation).
 * This is O(nb threads). Eventually use a hash table.
 */
void urcu_remove_reader(pthread_t id)
{
	struct reader_data *index;

	assert(reader_data != NULL);
	for (index = reader_data; index < reader_data + num_readers; index++) {
		if (pthread_equal(index->tid, id)) {
			memcpy(index, &reader_data[num_readers - 1],
				sizeof(struct reader_data));
			reader_data[num_readers - 1].tid = 0;
			reader_data[num_readers - 1].urcu_active_readers = NULL;
			num_readers--;
			return;
		}
	}
	/* Hrm not found, forgot to register ? */
	assert(0);
}

void urcu_register_thread(void)
{
	internal_urcu_lock();
	urcu_add_reader(pthread_self());
	internal_urcu_unlock();
}

void urcu_unregister_thread(void)
{
	internal_urcu_lock();
	urcu_remove_reader(pthread_self());
	internal_urcu_unlock();
}

#ifndef DEBUG_FULL_MB
void sigurcu_handler(int signo, siginfo_t *siginfo, void *context)
{
	/*
	 * Executing this smp_mb() is the only purpose of this signal handler.
	 * It punctually promotes barrier() into smp_mb() on every thread it is
	 * executed on.
	 */
	smp_mb();
	atomic_inc(&sig_done);
}

void __attribute__((constructor)) urcu_init(void)
{
	struct sigaction act;
	int ret;

	act.sa_sigaction = sigurcu_handler;
	ret = sigaction(SIGURCU, &act, NULL);
	if (ret) {
		perror("Error in sigaction");
		exit(-1);
	}
}

void __attribute__((destructor)) urcu_exit(void)
{
	struct sigaction act;
	int ret;

	ret = sigaction(SIGURCU, NULL, &act);
	if (ret) {
		perror("Error in sigaction");
		exit(-1);
	}
	assert(act.sa_sigaction == sigurcu_handler);
	free(reader_data);
}
#endif
