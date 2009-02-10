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
static int sig_done;

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
static void force_mb_all_threads(void)
{
	mb();
}
#else
static void force_mb_all_threads(void)
{
	struct reader_data *index;
	/*
	 * Ask for each threads to execute a mb() so we can consider the
	 * compiler barriers around rcu read lock as real memory barriers.
	 */
	if (!reader_data)
		return;
	debug_yield_write();
	sig_done = 0;
	debug_yield_write();
	mb();	/* write sig_done before sending the signals */
	debug_yield_write();
	for (index = reader_data; index < reader_data + num_readers; index++) {
		pthread_kill(index->tid, SIGURCU);
		debug_yield_write();
	}
	/*
	 * Wait for sighandler (and thus mb()) to execute on every thread.
	 * BUSY-LOOP.
	 */
	while (sig_done < num_readers)
		barrier();
	debug_yield_write();
	mb();	/* read sig_done before ending the barrier */
	debug_yield_write();
}
#endif

void wait_for_quiescent_state(void)
{
	struct reader_data *index;

	if (!reader_data)
		return;
	/* Wait for each thread urcu_active_readers count to become 0.
	 */
	for (index = reader_data; index < reader_data + num_readers; index++) {
		/*
		 * BUSY-LOOP.
		 */
		while (rcu_old_gp_ongoing(index->urcu_active_readers))
			barrier();
	}
	/*
	 * Locally : read *index->urcu_active_readers before freeing old
	 * pointer.
	 * Remote (reader threads) : Order urcu_qparity update and other
	 * thread's quiescent state counter read.
	 */
	force_mb_all_threads();
}

static void switch_qparity(void)
{
	/* All threads should read qparity before accessing data structure. */
	/* Write ptr before changing the qparity */
	force_mb_all_threads();
	debug_yield_write();
	switch_next_urcu_qparity();
	debug_yield_write();

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	wait_for_quiescent_state();
}

void synchronize_rcu(void)
{
	debug_yield_write();
	internal_urcu_lock();
	debug_yield_write();
	switch_qparity();
	debug_yield_write();
	switch_qparity();
	debug_yield_write();
	internal_urcu_unlock();
	debug_yield_write();
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
	mb();
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
