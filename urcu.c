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

/* Global quiescent period parity */
int urcu_qparity;

int __thread urcu_active_readers[2];

/* Thread IDs of registered readers */
#define INIT_NUM_THREADS 4

struct reader_data {
	pthread_t tid;
	int *urcu_active_readers;
};

static struct reader_data *reader_data;
static int num_readers, alloc_readers;
static int sig_done;

void rcu_write_lock(void)
{
	int ret;
	ret = pthread_mutex_lock(&urcu_mutex);
	if (ret) {
		perror("Error in pthread mutex lock");
		exit(-1);
	}
}

void rcu_write_unlock(void)
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
static int switch_next_urcu_qparity(void)
{
	int old_parity = urcu_qparity;
	urcu_qparity = 1 - old_parity;
	return old_parity;
}

static void force_mb_all_threads(void)
{
	struct reader_data *index;
	/*
	 * Ask for each threads to execute a mb() so we can consider the
	 * compiler barriers around rcu read lock as real memory barriers.
	 */
	if (!reader_data)
		return;
	sig_done = 0;
	mb();	/* write sig_done before sending the signals */
	for (index = reader_data; index < reader_data + num_readers; index++)
		pthread_kill(index->tid, SIGURCU);
	/*
	 * Wait for sighandler (and thus mb()) to execute on every thread.
	 * BUSY-LOOP.
	 */
	while (sig_done < num_readers)
		barrier();
	mb();	/* read sig_done before ending the barrier */
}

void wait_for_quiescent_state(int parity)
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
		while (index->urcu_active_readers[parity] != 0)
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

/*
 * Return old pointer, OK to free, no more reference exist.
 * Called under rcu_write_lock.
 */
void *_urcu_publish_content(void **ptr, void *new)
{
	int prev_parity;
	void *oldptr;

	/*
	 * We can publish the new pointer before we change the current qparity.
	 * Readers seeing the new pointer while being in the previous qparity
	 * window will make us wait until the end of the quiescent state before
	 * we release the unrelated memory area. However, given we hold the
	 * urcu_mutex, we are making sure that no further garbage collection can
	 * occur until we release the mutex, therefore we guarantee that this
	 * given reader will have completed its execution using the new pointer
	 * when the next quiescent state window will be over.
	 */
	oldptr = *ptr;
	*ptr = new;
	/* All threads should read qparity before ptr */
	/* Write ptr before changing the qparity */
	force_mb_all_threads();
	prev_parity = switch_next_urcu_qparity();

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	wait_for_quiescent_state(prev_parity);
	/*
	 * Deleting old data is ok !
	 */
	
	return oldptr;
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
	reader_data[num_readers].urcu_active_readers = urcu_active_readers;
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
		if (index->tid == id) {
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
	rcu_write_lock();
	urcu_add_reader(pthread_self());
	rcu_write_unlock();
}

void urcu_unregister_thread(void)
{
	rcu_write_lock();
	urcu_remove_reader(pthread_self());
	rcu_write_unlock();
}

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
