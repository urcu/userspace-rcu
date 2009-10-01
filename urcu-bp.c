/*
 * urcu-bp.c
 *
 * Userspace RCU library, "bulletproof" version.
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 *
 * IBM's contributions to this file may be relicensed under LGPLv2 or later.
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <pthread.h>
#include <signal.h>
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <poll.h>
#include <unistd.h>
#include <sys/mman.h>

#include "urcu-bp-static.h"
/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#include "urcu-bp.h"

/* Sleep delay in us */
#define RCU_SLEEP_DELAY		1000
#define ARENA_INIT_ALLOC	16

void __attribute__((destructor)) urcu_bp_exit(void);

static pthread_mutex_t urcu_mutex = PTHREAD_MUTEX_INITIALIZER;

#ifdef DEBUG_YIELD
unsigned int yield_active;
unsigned int __thread rand_yield;
#endif

/*
 * Global grace period counter.
 * Contains the current RCU_GP_CTR_BIT.
 * Also has a RCU_GP_COUNT of 1, to accelerate the reader fast path.
 * Written to only by writer with mutex taken. Read by both writer and readers.
 */
long urcu_gp_ctr = RCU_GP_COUNT;

/*
 * Pointer to registry elements. Written to only by each individual reader. Read
 * by both the reader and the writers.
 */
struct urcu_reader __thread *urcu_reader;

static LIST_HEAD(registry);

struct registry_arena {
	void *p;
	size_t len;
	size_t used;
};

static struct registry_arena registry_arena;

static void rcu_gc_registry(void);

static void internal_urcu_lock(void)
{
	int ret;

#ifndef DISTRUST_SIGNALS_EXTREME
	ret = pthread_mutex_lock(&urcu_mutex);
	if (ret) {
		perror("Error in pthread mutex lock");
		exit(-1);
	}
#else /* #ifndef DISTRUST_SIGNALS_EXTREME */
	while ((ret = pthread_mutex_trylock(&urcu_mutex)) != 0) {
		if (ret != EBUSY && ret != EINTR) {
			printf("ret = %d, errno = %d\n", ret, errno);
			perror("Error in pthread mutex lock");
			exit(-1);
		}
		if (urcu_reader.need_mb) {
			smp_mb();
			urcu_reader.need_mb = 0;
			smp_mb();
		}
		poll(NULL,0,10);
	}
#endif /* #else #ifndef DISTRUST_SIGNALS_EXTREME */
}

static void internal_urcu_unlock(void)
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
	STORE_SHARED(urcu_gp_ctr, urcu_gp_ctr ^ RCU_GP_CTR_BIT);
}

void wait_for_quiescent_state(void)
{
	LIST_HEAD(qsreaders);
	int wait_loops = 0;
	struct urcu_reader *index, *tmp;

	if (list_empty(&registry))
		return;
	/*
	 * Wait for each thread urcu_reader.ctr count to become 0.
	 */
	for (;;) {
		wait_loops++;
		list_for_each_entry_safe(index, tmp, &registry, head) {
			if (!rcu_old_gp_ongoing(&index->ctr))
				list_move(&index->head, &qsreaders);
		}

		if (list_empty(&registry)) {
			break;
		} else {
			if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS)
				usleep(RCU_SLEEP_DELAY);
			else
				cpu_relax();
		}
	}
	/* put back the reader list in the registry */
	list_splice(&qsreaders, &registry);
}

void synchronize_rcu(void)
{
	sigset_t newmask, oldmask;
	int ret;

	ret = sigemptyset(&newmask);
	assert(!ret);
	ret = pthread_sigmask(SIG_SETMASK, &newmask, &oldmask);
	assert(!ret);

	internal_urcu_lock();

	/* Remove old registry elements */
	rcu_gc_registry();

	/* All threads should read qparity before accessing data structure
	 * where new ptr points to. Must be done within internal_urcu_lock
	 * because it iterates on reader threads.*/
	/* Write new ptr before changing the qparity */
	smp_mb();

	switch_next_urcu_qparity();	/* 0 -> 1 */

	/*
	 * Must commit qparity update to memory before waiting for parity
	 * 0 quiescent state. Failure to do so could result in the writer
	 * waiting forever while new readers are always accessing data (no
	 * progress).
	 * Ensured by STORE_SHARED and LOAD_SHARED.
	 */

	/*
	 * Adding a smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	smp_mb();

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	wait_for_quiescent_state();	/* Wait readers in parity 0 */

	/*
	 * Must finish waiting for quiescent state for parity 0 before
	 * committing qparity update to memory. Failure to do so could result in
	 * the writer waiting forever while new readers are always accessing
	 * data (no progress).
	 * Ensured by STORE_SHARED and LOAD_SHARED.
	 */

	/*
	 * Adding a smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	smp_mb();

	switch_next_urcu_qparity();	/* 1 -> 0 */

	/*
	 * Must commit qparity update to memory before waiting for parity
	 * 1 quiescent state. Failure to do so could result in the writer
	 * waiting forever while new readers are always accessing data (no
	 * progress).
	 * Ensured by STORE_SHARED and LOAD_SHARED.
	 */

	/*
	 * Adding a smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	smp_mb();

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	wait_for_quiescent_state();	/* Wait readers in parity 1 */

	/* Finish waiting for reader threads before letting the old ptr being
	 * freed. Must be done within internal_urcu_lock because it iterates on
	 * reader threads. */
	smp_mb();

	internal_urcu_unlock();
	ret = pthread_sigmask(SIG_SETMASK, &oldmask, NULL);
	assert(!ret);
}

/*
 * library wrappers to be used by non-LGPL compatible source code.
 */

void rcu_read_lock(void)
{
	_rcu_read_lock();
}

void rcu_read_unlock(void)
{
	_rcu_read_unlock();
}

/*
 * only grow for now.
 */
static void resize_arena(struct registry_arena *arena, size_t len)
{
	void *new_arena;

	if (!arena->p)
		new_arena = mmap(arena->p, len,
				 PROT_READ | PROT_WRITE,
				 MAP_ANONYMOUS | MAP_PRIVATE,
				 -1, 0);
	else
		new_arena = mremap(arena->p, arena->len,
				   len, MREMAP_MAYMOVE);
	assert(new_arena != MAP_FAILED);

	/*
	 * re-used the same region ?
	 */
	if (new_arena == arena->p)
		return;

	memcpy(new_arena, arena->p, arena->len);
	bzero(new_arena + arena->len, len - arena->len);
	arena->p = new_arena;
}

/* Called with signals off and mutex locked */
static void add_thread(void)
{
	struct urcu_reader *urcu_reader_reg;

	if (registry_arena.len
	    < registry_arena.used + sizeof(struct urcu_reader))
		resize_arena(&registry_arena,
		max(registry_arena.len << 1, ARENA_INIT_ALLOC));
	/*
	 * Find a free spot.
	 */
	for (urcu_reader_reg = registry_arena.p;
	     (void *)urcu_reader_reg < registry_arena.p + registry_arena.len;
	     urcu_reader_reg++) {
		if (!urcu_reader_reg->alloc)
			break;
	}
	urcu_reader_reg->alloc = 1;
	registry_arena.used += sizeof(struct urcu_reader);

	/* Add to registry */
	urcu_reader_reg->tid = pthread_self();
	assert(urcu_reader_reg->ctr == 0);
	list_add(&urcu_reader_reg->head, &registry);
	urcu_reader = urcu_reader_reg;
}

/* Called with signals off and mutex locked */
static void rcu_gc_registry(void)
{
	struct urcu_reader *urcu_reader_reg;
	pthread_t tid;
	int ret;

	for (urcu_reader_reg = registry_arena.p;
	     (void *)urcu_reader_reg < registry_arena.p + registry_arena.len;
	     urcu_reader_reg++) {
		if (!urcu_reader_reg->alloc)
			continue;
		tid = urcu_reader_reg->tid;
		ret = pthread_kill(tid, 0);
		assert(ret != EINVAL);
		if (ret == ESRCH) {
			list_del(&urcu_reader_reg->head);
			urcu_reader_reg->alloc = 0;
			registry_arena.used -= sizeof(struct urcu_reader);
		}
	}
}

/* Disable signals, take mutex, add to registry */
void rcu_bp_register(void)
{
	sigset_t newmask, oldmask;
	int ret;

	ret = sigemptyset(&newmask);
	assert(!ret);
	ret = pthread_sigmask(SIG_SETMASK, &newmask, &oldmask);
	assert(!ret);

	/*
	 * Check if a signal concurrently registered our thread since
	 * the check in rcu_read_lock(). */
	if (urcu_reader)
		goto end;

	internal_urcu_lock();
	add_thread();
	internal_urcu_unlock();
end:
	ret = pthread_sigmask(SIG_SETMASK, &oldmask, NULL);
	assert(!ret);
}

void urcu_bp_exit()
{
	munmap(registry_arena.p, registry_arena.len);
}
