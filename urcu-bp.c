/*
 * urcu-bp.c
 *
 * Userspace RCU library, "bulletproof" version.
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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
#define _LGPL_SOURCE
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

#include "urcu/wfqueue.h"
#include "urcu/map/urcu-bp.h"
#include "urcu/static/urcu-bp.h"
#include "urcu-pointer.h"

/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#undef _LGPL_SOURCE
#include "urcu-bp.h"
#define _LGPL_SOURCE

#ifndef MAP_ANONYMOUS
#define MAP_ANONYMOUS MAP_ANON
#endif

#ifndef __linux__

#define MREMAP_MAYMOVE	1
#define MREMAP_FIXED	2

/*
 * mremap wrapper for non-Linux systems. Maps a RW, anonymous private mapping.
 * This is not generic.
*/
void *mremap(void *old_address, size_t old_size, size_t new_size, int flags)
{
	void *new_address;

	assert(flags & MREMAP_MAYMOVE);
	assert(!(flags & MREMAP_FIXED));
	new_address = mmap(old_address, new_size,
			   PROT_READ | PROT_WRITE,
			   MAP_ANONYMOUS | MAP_PRIVATE,
			   -1, 0);
	if (new_address == MAP_FAILED)
		return MAP_FAILED;
	if (old_address) {
		memcpy(new_address, old_address, old_size);
		munmap(old_address, old_size);
	}
	return new_address;
}
#endif

/* Sleep delay in us */
#define RCU_SLEEP_DELAY		1000
#define ARENA_INIT_ALLOC	16

/*
 * Active attempts to check for reader Q.S. before calling sleep().
 */
#define RCU_QS_ACTIVE_ATTEMPTS 100

void __attribute__((destructor)) rcu_bp_exit(void);

static pthread_mutex_t rcu_gp_lock = PTHREAD_MUTEX_INITIALIZER;

#ifdef DEBUG_YIELD
unsigned int yield_active;
unsigned int __thread rand_yield;
#endif

/*
 * Global grace period counter.
 * Contains the current RCU_GP_CTR_PHASE.
 * Also has a RCU_GP_COUNT of 1, to accelerate the reader fast path.
 * Written to only by writer with mutex taken. Read by both writer and readers.
 */
long rcu_gp_ctr = RCU_GP_COUNT;

/*
 * Pointer to registry elements. Written to only by each individual reader. Read
 * by both the reader and the writers.
 */
struct rcu_reader __thread *rcu_reader;

static CDS_LIST_HEAD(registry);

struct registry_arena {
	void *p;
	size_t len;
	size_t used;
};

static struct registry_arena registry_arena;

/* Saved fork signal mask, protected by rcu_gp_lock */
static sigset_t saved_fork_signal_mask;

static void rcu_gc_registry(void);

static void mutex_lock(pthread_mutex_t *mutex)
{
	int ret;

#ifndef DISTRUST_SIGNALS_EXTREME
	ret = pthread_mutex_lock(mutex);
	if (ret) {
		perror("Error in pthread mutex lock");
		exit(-1);
	}
#else /* #ifndef DISTRUST_SIGNALS_EXTREME */
	while ((ret = pthread_mutex_trylock(mutex)) != 0) {
		if (ret != EBUSY && ret != EINTR) {
			printf("ret = %d, errno = %d\n", ret, errno);
			perror("Error in pthread mutex lock");
			exit(-1);
		}
		poll(NULL,0,10);
	}
#endif /* #else #ifndef DISTRUST_SIGNALS_EXTREME */
}

static void mutex_unlock(pthread_mutex_t *mutex)
{
	int ret;

	ret = pthread_mutex_unlock(mutex);
	if (ret) {
		perror("Error in pthread mutex unlock");
		exit(-1);
	}
}

void update_counter_and_wait(void)
{
	CDS_LIST_HEAD(qsreaders);
	int wait_loops = 0;
	struct rcu_reader *index, *tmp;

	/* Switch parity: 0 -> 1, 1 -> 0 */
	CMM_STORE_SHARED(rcu_gp_ctr, rcu_gp_ctr ^ RCU_GP_CTR_PHASE);

	/*
	 * Must commit qparity update to memory before waiting for other parity
	 * quiescent state. Failure to do so could result in the writer waiting
	 * forever while new readers are always accessing data (no progress).
	 * Ensured by CMM_STORE_SHARED and CMM_LOAD_SHARED.
	 */

	/*
	 * Adding a cmm_smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	cmm_smp_mb();

	/*
	 * Wait for each thread rcu_reader.ctr count to become 0.
	 */
	for (;;) {
		wait_loops++;
		cds_list_for_each_entry_safe(index, tmp, &registry, node) {
			if (!rcu_old_gp_ongoing(&index->ctr))
				cds_list_move(&index->node, &qsreaders);
		}

		if (cds_list_empty(&registry)) {
			break;
		} else {
			if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS)
				usleep(RCU_SLEEP_DELAY);
			else
				caa_cpu_relax();
		}
	}
	/* put back the reader list in the registry */
	cds_list_splice(&qsreaders, &registry);
}

void synchronize_rcu(void)
{
	sigset_t newmask, oldmask;
	int ret;

	ret = sigemptyset(&newmask);
	assert(!ret);
	ret = pthread_sigmask(SIG_SETMASK, &newmask, &oldmask);
	assert(!ret);

	mutex_lock(&rcu_gp_lock);

	if (cds_list_empty(&registry))
		goto out;

	/* All threads should read qparity before accessing data structure
	 * where new ptr points to. */
	/* Write new ptr before changing the qparity */
	cmm_smp_mb();

	/* Remove old registry elements */
	rcu_gc_registry();

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	update_counter_and_wait();	/* 0 -> 1, wait readers in parity 0 */

	/*
	 * Adding a cmm_smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	cmm_smp_mb();

	/*
	 * Wait for previous parity to be empty of readers.
	 */
	update_counter_and_wait();	/* 1 -> 0, wait readers in parity 1 */

	/*
	 * Finish waiting for reader threads before letting the old ptr being
	 * freed.
	 */
	cmm_smp_mb();
out:
	mutex_unlock(&rcu_gp_lock);
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

	bzero(new_arena + arena->len, len - arena->len);
	arena->p = new_arena;
}

/* Called with signals off and mutex locked */
static void add_thread(void)
{
	struct rcu_reader *rcu_reader_reg;

	if (registry_arena.len
	    < registry_arena.used + sizeof(struct rcu_reader))
		resize_arena(&registry_arena,
		caa_max(registry_arena.len << 1, ARENA_INIT_ALLOC));
	/*
	 * Find a free spot.
	 */
	for (rcu_reader_reg = registry_arena.p;
	     (void *)rcu_reader_reg < registry_arena.p + registry_arena.len;
	     rcu_reader_reg++) {
		if (!rcu_reader_reg->alloc)
			break;
	}
	rcu_reader_reg->alloc = 1;
	registry_arena.used += sizeof(struct rcu_reader);

	/* Add to registry */
	rcu_reader_reg->tid = pthread_self();
	assert(rcu_reader_reg->ctr == 0);
	cds_list_add(&rcu_reader_reg->node, &registry);
	rcu_reader = rcu_reader_reg;
}

/* Called with signals off and mutex locked */
static void rcu_gc_registry(void)
{
	struct rcu_reader *rcu_reader_reg;
	pthread_t tid;
	int ret;

	for (rcu_reader_reg = registry_arena.p;
	     (void *)rcu_reader_reg < registry_arena.p + registry_arena.len;
	     rcu_reader_reg++) {
		if (!rcu_reader_reg->alloc)
			continue;
		tid = rcu_reader_reg->tid;
		ret = pthread_kill(tid, 0);
		assert(ret != EINVAL);
		if (ret == ESRCH) {
			cds_list_del(&rcu_reader_reg->node);
			rcu_reader_reg->ctr = 0;
			rcu_reader_reg->alloc = 0;
			registry_arena.used -= sizeof(struct rcu_reader);
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
	if (rcu_reader)
		goto end;

	mutex_lock(&rcu_gp_lock);
	add_thread();
	mutex_unlock(&rcu_gp_lock);
end:
	ret = pthread_sigmask(SIG_SETMASK, &oldmask, NULL);
	assert(!ret);
}

void rcu_bp_exit(void)
{
	if (registry_arena.p)
		munmap(registry_arena.p, registry_arena.len);
}

/*
 * Holding the rcu_gp_lock across fork will make sure we fork() don't race with
 * a concurrent thread executing with this same lock held. This ensures that the
 * registry is in a coherent state in the child.
 */
void rcu_bp_before_fork(void)
{
	sigset_t newmask, oldmask;
	int ret;

	ret = sigemptyset(&newmask);
	assert(!ret);
	ret = pthread_sigmask(SIG_SETMASK, &newmask, &oldmask);
	assert(!ret);
	mutex_lock(&rcu_gp_lock);
	saved_fork_signal_mask = oldmask;
}

void rcu_bp_after_fork_parent(void)
{
	sigset_t oldmask;
	int ret;

	oldmask = saved_fork_signal_mask;
	mutex_unlock(&rcu_gp_lock);
	ret = pthread_sigmask(SIG_SETMASK, &oldmask, NULL);
	assert(!ret);
}

void rcu_bp_after_fork_child(void)
{
	sigset_t oldmask;
	int ret;

	rcu_gc_registry();
	oldmask = saved_fork_signal_mask;
	mutex_unlock(&rcu_gp_lock);
	ret = pthread_sigmask(SIG_SETMASK, &oldmask, NULL);
	assert(!ret);
}

#include "urcu-call-rcu-impl.h"
#include "urcu-defer-impl.h"
