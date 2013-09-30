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

#include "urcu/wfcqueue.h"
#include "urcu/map/urcu-bp.h"
#include "urcu/static/urcu-bp.h"
#include "urcu-pointer.h"
#include "urcu/tls-compat.h"

#include "urcu-die.h"

/* Do not #define _LGPL_SOURCE to ensure we can emit the wrapper symbols */
#undef _LGPL_SOURCE
#include "urcu-bp.h"
#define _LGPL_SOURCE

#ifndef MAP_ANONYMOUS
#define MAP_ANONYMOUS MAP_ANON
#endif

#ifdef __linux__
static
void *mremap_wrapper(void *old_address, size_t old_size,
		size_t new_size, int flags)
{
	return mremap(old_address, old_size, new_size, flags);
}
#else

#define MREMAP_MAYMOVE	1
#define MREMAP_FIXED	2

/*
 * mremap wrapper for non-Linux systems. Maps a RW, anonymous private mapping.
 * This is not generic.
*/
static
void *mremap_wrapper(void *old_address, size_t old_size,
		size_t new_size, int flags)
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
unsigned int rcu_yield_active;
DEFINE_URCU_TLS(unsigned int, rcu_rand_yield);
#endif

struct rcu_gp rcu_gp = { .ctr = RCU_GP_COUNT };

/*
 * Pointer to registry elements. Written to only by each individual reader. Read
 * by both the reader and the writers.
 */
DEFINE_URCU_TLS(struct rcu_reader *, rcu_reader);

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
	if (ret)
		urcu_die(ret);
#else /* #ifndef DISTRUST_SIGNALS_EXTREME */
	while ((ret = pthread_mutex_trylock(mutex)) != 0) {
		if (ret != EBUSY && ret != EINTR)
			urcu_die(ret);
		poll(NULL,0,10);
	}
#endif /* #else #ifndef DISTRUST_SIGNALS_EXTREME */
}

static void mutex_unlock(pthread_mutex_t *mutex)
{
	int ret;

	ret = pthread_mutex_unlock(mutex);
	if (ret)
		urcu_die(ret);
}

static void wait_for_readers(struct cds_list_head *input_readers,
			struct cds_list_head *cur_snap_readers,
			struct cds_list_head *qsreaders)
{
	int wait_loops = 0;
	struct rcu_reader *index, *tmp;

	/*
	 * Wait for each thread URCU_TLS(rcu_reader).ctr to either
	 * indicate quiescence (not nested), or observe the current
	 * rcu_gp.ctr value.
	 */
	for (;;) {
		wait_loops++;
		cds_list_for_each_entry_safe(index, tmp, input_readers, node) {
			switch (rcu_reader_state(&index->ctr)) {
			case RCU_READER_ACTIVE_CURRENT:
				if (cur_snap_readers) {
					cds_list_move(&index->node,
						cur_snap_readers);
					break;
				}
				/* Fall-through */
			case RCU_READER_INACTIVE:
				cds_list_move(&index->node, qsreaders);
				break;
			case RCU_READER_ACTIVE_OLD:
				/*
				 * Old snapshot. Leaving node in
				 * input_readers will make us busy-loop
				 * until the snapshot becomes current or
				 * the reader becomes inactive.
				 */
				break;
			}
		}

		if (cds_list_empty(input_readers)) {
			break;
		} else {
			if (wait_loops == RCU_QS_ACTIVE_ATTEMPTS)
				usleep(RCU_SLEEP_DELAY);
			else
				caa_cpu_relax();
		}
	}
}

void synchronize_rcu(void)
{
	CDS_LIST_HEAD(cur_snap_readers);
	CDS_LIST_HEAD(qsreaders);
	sigset_t newmask, oldmask;
	int ret;

	ret = sigfillset(&newmask);
	assert(!ret);
	ret = pthread_sigmask(SIG_BLOCK, &newmask, &oldmask);
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
	 * Wait for readers to observe original parity or be quiescent.
	 */
	wait_for_readers(&registry, &cur_snap_readers, &qsreaders);

	/*
	 * Adding a cmm_smp_mb() which is _not_ formally required, but makes the
	 * model easier to understand. It does not have a big performance impact
	 * anyway, given this is the write-side.
	 */
	cmm_smp_mb();

	/* Switch parity: 0 -> 1, 1 -> 0 */
	CMM_STORE_SHARED(rcu_gp.ctr, rcu_gp.ctr ^ RCU_GP_CTR_PHASE);

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
	 * Wait for readers to observe new parity or be quiescent.
	 */
	wait_for_readers(&cur_snap_readers, NULL, &qsreaders);

	/*
	 * Put quiescent reader list back into registry.
	 */
	cds_list_splice(&qsreaders, &registry);

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

int rcu_read_ongoing(void)
{
	return _rcu_read_ongoing();
}

/*
 * only grow for now.
 */
static void resize_arena(struct registry_arena *arena, size_t len)
{
	void *new_p;
	size_t old_len;

	old_len = arena->len;

	if (!arena->p)
		new_p = mmap(arena->p, len,
			PROT_READ | PROT_WRITE,
			MAP_ANONYMOUS | MAP_PRIVATE,
			-1, 0);
	else
		new_p = mremap_wrapper(arena->p, old_len,
			len, MREMAP_MAYMOVE);
	assert(new_p != MAP_FAILED);

	/*
	 * Zero the newly allocated memory. Since mmap() does not
	 * clearly specify if memory is zeroed or not (although it is
	 * very likely that it is), be extra careful by not expecting
	 * the new range to be zeroed by mremap.
	 */
	bzero(new_p + old_len, len - old_len);

	/*
	 * If we did not re-use the same region, we need to update the
	 * arena pointer.
	 */
	if (new_p != arena->p)
		arena->p = new_p;

	arena->len = len;
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
	URCU_TLS(rcu_reader) = rcu_reader_reg;
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

	ret = sigfillset(&newmask);
	assert(!ret);
	ret = pthread_sigmask(SIG_BLOCK, &newmask, &oldmask);
	assert(!ret);

	/*
	 * Check if a signal concurrently registered our thread since
	 * the check in rcu_read_lock(). */
	if (URCU_TLS(rcu_reader))
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

	ret = sigfillset(&newmask);
	assert(!ret);
	ret = pthread_sigmask(SIG_BLOCK, &newmask, &oldmask);
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

void *rcu_dereference_sym_bp(void *p)
{
	return _rcu_dereference(p);
}

void *rcu_set_pointer_sym_bp(void **p, void *v)
{
	cmm_wmb();
	uatomic_set(p, v);
	return v;
}

void *rcu_xchg_pointer_sym_bp(void **p, void *v)
{
	cmm_wmb();
	return uatomic_xchg(p, v);
}

void *rcu_cmpxchg_pointer_sym_bp(void **p, void *old, void *_new)
{
	cmm_wmb();
	return uatomic_cmpxchg(p, old, _new);
}

DEFINE_RCU_FLAVOR(rcu_flavor);

#include "urcu-call-rcu-impl.h"
#include "urcu-defer-impl.h"
