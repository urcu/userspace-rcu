#ifndef _TEST_URCU_JA_H
#define _TEST_URCU_JA_H

/*
 * test_urcu_ja.h
 *
 * Userspace RCU library - test program
 *
 * Copyright 2009-2012 - Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
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
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdio.h>
#include <assert.h>
#include <sched.h>
#include <errno.h>
#include <signal.h>

#include <urcu/tls-compat.h>
#include "thread-id.h"

#define DEFAULT_RAND_POOL	1000000

/* Make this big enough to include the POWER5+ L3 cacheline size of 256B */
#define CACHE_LINE_SIZE 4096

/* hardcoded number of CPUs */
#define NR_CPUS 16384

#ifdef POISON_FREE
#define poison_free(ptr)				\
	do {						\
		memset(ptr, 0x42, sizeof(*(ptr)));	\
		free(ptr);				\
	} while (0)
#else
#define poison_free(ptr)	free(ptr)
#endif

#ifndef DYNAMIC_LINK_TEST
#define _LGPL_SOURCE
#else
#define debug_yield_read()
#endif
#include <urcu-qsbr.h>
#include <urcu/rcuja.h>
#include <urcu-call-rcu.h>

struct wr_count {
	unsigned long update_ops;
	unsigned long add;
	unsigned long add_exist;
	unsigned long remove;
};

extern DECLARE_URCU_TLS(unsigned int, rand_lookup);
extern DECLARE_URCU_TLS(unsigned long, nr_add);
extern DECLARE_URCU_TLS(unsigned long, nr_addexist);
extern DECLARE_URCU_TLS(unsigned long, nr_del);
extern DECLARE_URCU_TLS(unsigned long, nr_delnoent);
extern DECLARE_URCU_TLS(unsigned long, lookup_fail);
extern DECLARE_URCU_TLS(unsigned long, lookup_ok);

extern struct cds_ja *test_ja;

struct ja_test_node {
	struct cds_ja_node node;
	uint64_t key;		/* for testing */
	struct rcu_head head;	/* delayed reclaim */
};

static inline struct ja_test_node *
to_test_node(struct cds_ja_node *node)
{
	return caa_container_of(node, struct ja_test_node, node);
}

static inline
void ja_test_node_init(struct ja_test_node *node, uint64_t key)
{
	cds_ja_node_init(&node->node);
	node->key = key;
}

extern volatile int test_go, test_stop;

extern unsigned long wdelay;

extern unsigned long duration;

/* read-side C.S. duration, in loops */
extern unsigned long rduration;

extern unsigned long init_populate;
extern int add_only;

extern unsigned long init_pool_offset, lookup_pool_offset, write_pool_offset;
extern unsigned long init_pool_size,
	lookup_pool_size,
	write_pool_size;
extern int validate_lookup;

extern int count_pipe[2];

static inline void loop_sleep(unsigned long l)
{
	while(l-- != 0)
		caa_cpu_relax();
}

extern int verbose_mode;

#define printf_verbose(fmt, args...)		\
	do {					\
		if (verbose_mode)		\
			printf(fmt, ## args);	\
	} while (0)

extern unsigned int cpu_affinities[NR_CPUS];
extern unsigned int next_aff;
extern int use_affinity;

extern pthread_mutex_t affinity_mutex;

#ifndef HAVE_CPU_SET_T
typedef unsigned long cpu_set_t;
# define CPU_ZERO(cpuset) do { *(cpuset) = 0; } while(0)
# define CPU_SET(cpu, cpuset) do { *(cpuset) |= (1UL << (cpu)); } while(0)
#endif

void set_affinity(void);

/*
 * returns 0 if test should end.
 */
static inline int test_duration_write(void)
{
	return !test_stop;
}

static inline int test_duration_read(void)
{
	return !test_stop;
}

extern DECLARE_URCU_TLS(unsigned long long, nr_writes);
extern DECLARE_URCU_TLS(unsigned long long, nr_reads);

extern unsigned int nr_readers;
extern unsigned int nr_writers;

void rcu_copy_mutex_lock(void);
void rcu_copy_mutex_unlock(void);

#endif /* _TEST_URCU_JA_H */
