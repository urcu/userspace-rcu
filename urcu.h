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

/* Global quiescent period parity */
extern int urcu_qparity;

extern int __thread urcu_active_readers[2];

static inline int get_urcu_qparity(void)
{
	return urcu_qparity;
}

/*
 * returns urcu_parity.
 */
static inline int rcu_read_lock(void)
{
	int urcu_parity = get_urcu_qparity();
	urcu_active_readers[urcu_parity]++;
	/*
	 * Increment active readers count before accessing the pointer.
	 * See force_mb_all_threads().
	 */
	barrier();
	return urcu_parity;
}

static inline void rcu_read_unlock(int urcu_parity)
{
	barrier();
	/*
	 * Finish using rcu before decrementing the pointer.
	 * See force_mb_all_threads().
	 */
	urcu_active_readers[urcu_parity]--;
}

extern void rcu_write_lock(void);
extern void rcu_write_unlock(void);

extern void *_urcu_publish_content(void **ptr, void *new);

/*
 * gcc does not like automatic &struct ... * -> void **.
 * Remove the warning. (hopefully this is ok)
 */
#define urcu_publish_content(ptr, new) _urcu_publish_content((void **)ptr, new)

/*
 * Reader thread registration.
 */
extern void urcu_register_thread(void);
extern void urcu_unregister_thread(void);

#endif /* _URCU_H */
