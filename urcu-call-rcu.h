#ifndef _URCU_CALL_RCU_H
#define _URCU_CALL_RCU_H

/*
 * urcu-call-rcu.h
 *
 * Userspace RCU header - deferred execution
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 *
 * LGPL-compatible code should include this header with :
 *
 * #define _LGPL_SOURCE
 * #include <urcu-defer.h>
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
 */

#include <stdlib.h>
#include <pthread.h>

#include <urcu/wfqueue.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Note that struct call_rcu_data is opaque to callers. */

struct call_rcu_data;

/* Flag values. */

#define URCU_CALL_RCU_RT	0x1
#define URCU_CALL_RCU_RUNNING	0x2
#define URCU_CALL_RCU_STOP	0x4
#define URCU_CALL_RCU_STOPPED	0x8

/*
 * The rcu_head data structure is placed in the structure to be freed
 * via call_rcu().
 */

struct rcu_head {
	struct cds_wfq_node next;
	void (*func)(struct rcu_head *head);
};

/*
 * Exported functions
 *
 * Important: see userspace RCU API.txt for call_rcu family of functions
 * usage detail, including the surrounding RCU usage required when using
 * these primitives.
 */

void call_rcu(struct rcu_head *head,
	      void (*func)(struct rcu_head *head));

struct call_rcu_data *create_call_rcu_data(unsigned long flags,
					   int cpu_affinity);
void call_rcu_data_free(struct call_rcu_data *crdp);

struct call_rcu_data *get_default_call_rcu_data(void);
struct call_rcu_data *get_cpu_call_rcu_data(int cpu);
struct call_rcu_data *get_thread_call_rcu_data(void);
struct call_rcu_data *get_call_rcu_data(void);
pthread_t get_call_rcu_thread(struct call_rcu_data *crdp);

void set_thread_call_rcu_data(struct call_rcu_data *crdp);
int set_cpu_call_rcu_data(int cpu, struct call_rcu_data *crdp);

int create_all_cpu_call_rcu_data(unsigned long flags);
void free_all_cpu_call_rcu_data(void);

void call_rcu_after_fork_child(void);

#ifdef __cplusplus 
}
#endif

#endif /* _URCU_CALL_RCU_H */
