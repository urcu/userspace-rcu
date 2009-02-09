#ifndef _URCU_H
#define _URCU_H

/*
 * urcu.h
 *
 * Userspace RCU header
 *
 * Copyright February 2009 - Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
 *
 * Credits for Paul e. McKenney <paulmck@linux.vnet.ibm.com>
 * for inspiration coming from the Linux kernel RCU and rcu-preempt.
 *
 * The barrier, mb, rmb, wmb, atomic_inc, smp_read_barrier_depends, ACCESS_ONCE
 * and rcu_dereference primitives come from the Linux kernel.
 *
 * Distributed under GPLv2
 */

#include <stdlib.h>

/* The "volatile" is due to gcc bugs */
#define barrier() __asm__ __volatile__("": : :"memory")

/* x86 32/64 specific */
#define mb()    asm volatile("mfence":::"memory")
#define rmb()   asm volatile("lfence":::"memory")
#define wmb()   asm volatile("sfence" ::: "memory")

static inline void atomic_inc(int *v)
{
	asm volatile("lock; incl %0"
		     : "+m" (*v));
}

/* Nop everywhere except on alpha. */
#define smp_read_barrier_depends()

/*
 * Prevent the compiler from merging or refetching accesses.  The compiler
 * is also forbidden from reordering successive instances of ACCESS_ONCE(),
 * but only when the compiler is aware of some particular ordering.  One way
 * to make the compiler aware of ordering is to put the two invocations of
 * ACCESS_ONCE() in different C statements.
 *
 * This macro does absolutely -nothing- to prevent the CPU from reordering,
 * merging, or refetching absolutely anything at any time.  Its main intended
 * use is to mediate communication between process-level code and irq/NMI
 * handlers, all running on the same CPU.
 */
#define ACCESS_ONCE(x) (*(volatile typeof(x) *)&(x))

/**
 * rcu_dereference - fetch an RCU-protected pointer in an
 * RCU read-side critical section.  This pointer may later
 * be safely dereferenced.
 *
 * Inserts memory barriers on architectures that require them
 * (currently only the Alpha), and, more importantly, documents
 * exactly which pointers are protected by RCU.
 */

#define rcu_dereference(p)     ({ \
				typeof(p) _________p1 = ACCESS_ONCE(p); \
				smp_read_barrier_depends(); \
				(_________p1); \
				})

#define SIGURCU SIGUSR1

#ifdef DEBUG_YIELD
#include <sched.h>

#define YIELD_READ 	(1 << 0)
#define YIELD_WRITE	(1 << 1)

extern unsigned int yield_active;
extern unsigned int __thread rand_yield;

static inline void debug_yield_read(void)
{
	if (yield_active & YIELD_READ)
		if (rand_r(&rand_yield) & 0x1)
			sched_yield();
}

static inline void debug_yield_write(void)
{
	if (yield_active & YIELD_WRITE)
		if (rand_r(&rand_yield) & 0x1)
			sched_yield();
}

static inline void debug_yield_init(void)
{
	rand_yield = time(NULL) ^ pthread_self();
}
#else
static inline void debug_yield_read(void)
{
}

static inline void debug_yield_write(void)
{
}

static inline void debug_yield_init(void)
{

}
#endif

/*
 * Limiting the nesting level to 256 to keep instructions small in the read
 * fast-path.
 */
#define RCU_GP_COUNT		(1U << 0)
#define RCU_GP_CTR_BIT		(1U << 8)
#define RCU_GP_CTR_NEST_MASK	(RCU_GP_CTR_BIT - 1)

/* Global quiescent period counter with low-order bits unused. */
extern int urcu_gp_ctr;

extern int __thread urcu_active_readers;

static inline int rcu_old_gp_ongoing(int *value)
{
	int v;

	if (value == NULL)
		return 0;
	debug_yield_write();
	v = ACCESS_ONCE(*value);
	debug_yield_write();
	return (v & RCU_GP_CTR_NEST_MASK) &&
		 ((v ^ ACCESS_ONCE(urcu_gp_ctr)) & RCU_GP_CTR_BIT);
}

static inline void rcu_read_lock(void)
{
	int tmp;

	debug_yield_read();
	tmp = urcu_active_readers;
	debug_yield_read();
	if (!(tmp & RCU_GP_CTR_NEST_MASK))
		urcu_active_readers = urcu_gp_ctr + RCU_GP_COUNT;
	else
		urcu_active_readers = tmp + RCU_GP_COUNT;
	debug_yield_read();
	/*
	 * Increment active readers count before accessing the pointer.
	 * See force_mb_all_threads().
	 */
	barrier();
	debug_yield_read();
}

static inline void rcu_read_unlock(void)
{
	debug_yield_read();
	barrier();
	debug_yield_read();
	/*
	 * Finish using rcu before decrementing the pointer.
	 * See force_mb_all_threads().
	 */
	urcu_active_readers -= RCU_GP_COUNT;
	debug_yield_read();
}

extern void *urcu_publish_content(void **ptr, void *new);

/*
 * Reader thread registration.
 */
extern void urcu_register_thread(void);
extern void urcu_unregister_thread(void);

#endif /* _URCU_H */
