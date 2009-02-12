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
#include <pthread.h>

/* The "volatile" is due to gcc bugs */
#define barrier() __asm__ __volatile__("": : :"memory")

#define likely(x)       __builtin_expect(!!(x), 1)
#define unlikely(x)     __builtin_expect(!!(x), 0)

/*
 * Assume the architecture has coherent caches. Blackfin will want this unset.
 */
#define CONFIG_HAVE_MEM_COHERENCY 1

/* Assume P4 or newer */
#define CONFIG_HAVE_FENCE 1

/* Assume SMP machine, given we don't have this information */
#define CONFIG_SMP 1


#ifdef CONFIG_HAVE_MEM_COHERENCY
/*
 * Caches are coherent, no need to flush them.
 */
#define mc()	barrier()
#define rmc()	barrier()
#define wmc()	barrier()
#else
#error "The architecture must create its own cache flush primitives"
#define mc()	arch_cache_flush()
#define rmc()	arch_cache_flush_read()
#define wmc()	arch_cache_flush_write()
#endif


#ifdef CONFIG_HAVE_MEM_COHERENCY

/* x86 32/64 specific */
#ifdef CONFIG_HAVE_FENCE
#define mb()    asm volatile("mfence":::"memory")
#define rmb()   asm volatile("lfence":::"memory")
#define wmb()   asm volatile("sfence"::: "memory")
#else
/*
 * Some non-Intel clones support out of order store. wmb() ceases to be a
 * nop for these.
 */
#define mb()    asm volatile("lock; addl $0,0(%%esp)":::"memory")
#define rmb()   asm volatile("lock; addl $0,0(%%esp)":::"memory")
#define wmb()   asm volatile("lock; addl $0,0(%%esp)"::: "memory")
#endif

#else /* !CONFIG_HAVE_MEM_COHERENCY */

/*
 * Without cache coherency, the memory barriers become cache flushes.
 */
#define mb()    mc()
#define rmb()   rmc()
#define wmb()   wmc()

#endif /* !CONFIG_HAVE_MEM_COHERENCY */


#ifdef CONFIG_SMP
#define smp_mb()	mb()
#define smp_rmb()	rmb()
#define smp_wmb()	wmb()
#define smp_mc()	mc()
#define smp_rmc()	rmc()
#define smp_wmc()	wmc()
#else
#define smp_mb()	barrier()
#define smp_rmb()	barrier()
#define smp_wmb()	barrier()
#define smp_mc()	barrier()
#define smp_rmc()	barrier()
#define smp_wmc()	barrier()
#endif

/* REP NOP (PAUSE) is a good thing to insert into busy-wait loops. */
static inline void rep_nop(void)
{
	asm volatile("rep; nop" ::: "memory");
}

static inline void cpu_relax(void)
{
	rep_nop();
}

static inline void atomic_inc(int *v)
{
	asm volatile("lock; incl %0"
		     : "+m" (*v));
}

#define xchg(ptr, v)							\
	((__typeof__(*(ptr)))__xchg((unsigned long)(v), (ptr), sizeof(*(ptr))))

struct __xchg_dummy {
	unsigned long a[100];
};
#define __xg(x) ((struct __xchg_dummy *)(x))

/*
 * Note: no "lock" prefix even on SMP: xchg always implies lock anyway
 * Note 2: xchg has side effect, so that attribute volatile is necessary,
 *	  but generally the primitive is invalid, *ptr is output argument. --ANK
 * x is considered local, ptr is considered remote.
 */
static inline unsigned long __xchg(unsigned long x, volatile void *ptr,
				   int size)
{
	switch (size) {
	case 1:
		asm volatile("xchgb %b0,%1"
			     : "=q" (x)
			     : "m" (*__xg(ptr)), "0" (x)
			     : "memory");
		break;
	case 2:
		asm volatile("xchgw %w0,%1"
			     : "=r" (x)
			     : "m" (*__xg(ptr)), "0" (x)
			     : "memory");
		break;
	case 4:
		asm volatile("xchgl %k0,%1"
			     : "=r" (x)
			     : "m" (*__xg(ptr)), "0" (x)
			     : "memory");
		break;
	case 8:
		asm volatile("xchgq %0,%1"
			     : "=r" (x)
			     : "m" (*__xg(ptr)), "0" (x)
			     : "memory");
		break;
	}
	smp_wmc();
	return x;
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

/*
 * Load a data from remote memory, doing a cache flush if required.
 */
#define LOAD_REMOTE(p)	       ({ \
				smp_rmc(); \
				typeof(p) _________p1 = ACCESS_ONCE(p); \
				(_________p1); \
				})

/*
 * Store v into x, where x is located in remote memory. Performs the required
 * cache flush after writing.
 */
#define STORE_REMOTE(x, v) \
	do { \
		(x) = (v); \
		smp_wmc; \
	} while (0)

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
				typeof(p) _________p1 = LOAD_REMOTE(p); \
				smp_read_barrier_depends(); \
				(_________p1); \
				})



#define SIGURCU SIGUSR1

/*
 * If a reader is really non-cooperative and refuses to commit its
 * urcu_active_readers count to memory (there is no barrier in the reader
 * per-se), kick it after a few loops waiting for it.
 */
#define KICK_READER_LOOPS 10000

#ifdef DEBUG_YIELD
#include <sched.h>
#include <time.h>
#include <pthread.h>
#include <unistd.h>

#define YIELD_READ 	(1 << 0)
#define YIELD_WRITE	(1 << 1)

/* Updates without DEBUG_FULL_MB are much slower. Account this in the delay */
#ifdef DEBUG_FULL_MB
/* maximum sleep delay, in us */
#define MAX_SLEEP 50
#else
#define MAX_SLEEP 30000
#endif

extern unsigned int yield_active;
extern unsigned int __thread rand_yield;

static inline void debug_yield_read(void)
{
	if (yield_active & YIELD_READ)
		if (rand_r(&rand_yield) & 0x1)
			usleep(rand_r(&rand_yield) % MAX_SLEEP);
}

static inline void debug_yield_write(void)
{
	if (yield_active & YIELD_WRITE)
		if (rand_r(&rand_yield) & 0x1)
			usleep(rand_r(&rand_yield) % MAX_SLEEP);
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

#ifdef DEBUG_FULL_MB
static inline void reader_barrier()
{
	smp_mb();
}
#else
static inline void reader_barrier()
{
	barrier();
}
#endif

/*
 * The trick here is that RCU_GP_CTR_BIT must be a multiple of 8 so we can use a
 * full 8-bits, 16-bits or 32-bits bitmask for the lower order bits.
 */
#define RCU_GP_COUNT		(1UL << 0)
/* Use the amount of bits equal to half of the architecture long size */
#define RCU_GP_CTR_BIT		(1UL << (sizeof(long) << 2))
#define RCU_GP_CTR_NEST_MASK	(RCU_GP_CTR_BIT - 1)

/*
 * Global quiescent period counter with low-order bits unused.
 * Using a int rather than a char to eliminate false register dependencies
 * causing stalls on some architectures.
 */
extern long urcu_gp_ctr;

extern long __thread urcu_active_readers;

static inline int rcu_old_gp_ongoing(long *value)
{
	long v;

	if (value == NULL)
		return 0;
	/*
	 * Make sure both tests below are done on the same version of *value
	 * to insure consistency.
	 */
	v = LOAD_REMOTE(*value);
	return (v & RCU_GP_CTR_NEST_MASK) &&
		 ((v ^ urcu_gp_ctr) & RCU_GP_CTR_BIT);
}

static inline void rcu_read_lock(void)
{
	long tmp;

	tmp = urcu_active_readers;
	/* urcu_gp_ctr = RCU_GP_COUNT | (~RCU_GP_CTR_BIT or RCU_GP_CTR_BIT) */
	/*
	 * The data dependency "read urcu_gp_ctr, write urcu_active_readers",
	 * serializes those two memory operations. We are not using STORE_REMOTE
	 * and LOAD_REMOTE here (although we should) because the writer will
	 * wake us up with a signal which does a flush in its handler to perform
	 * urcu_gp_ctr re-read and urcu_active_readers commit to main memory.
	 */
	if (likely(!(tmp & RCU_GP_CTR_NEST_MASK)))
		urcu_active_readers = ACCESS_ONCE(urcu_gp_ctr);
	else
		urcu_active_readers = tmp + RCU_GP_COUNT;
	/*
	 * Increment active readers count before accessing the pointer.
	 * See force_mb_all_threads().
	 */
	reader_barrier();
}

static inline void rcu_read_unlock(void)
{
	reader_barrier();
	/*
	 * Finish using rcu before decrementing the pointer.
	 * See force_mb_all_threads().
	 */
	urcu_active_readers -= RCU_GP_COUNT;
}

/**
 * rcu_assign_pointer - assign (publicize) a pointer to a newly
 * initialized structure that will be dereferenced by RCU read-side
 * critical sections.  Returns the value assigned.
 *
 * Inserts memory barriers on architectures that require them
 * (pretty much all of them other than x86), and also prevents
 * the compiler from reordering the code that initializes the
 * structure after the pointer assignment.  More importantly, this
 * call documents which pointers will be dereferenced by RCU read-side
 * code.
 */

#define rcu_assign_pointer(p, v) \
	({ \
		if (!__builtin_constant_p(v) || \
		    ((v) != NULL)) \
			wmb(); \
		(p) = (v); \
		smp_wmc(); \
	})

#define rcu_xchg_pointer(p, v) \
	({ \
		if (!__builtin_constant_p(v) || \
		    ((v) != NULL)) \
			wmb(); \
		xchg(p, v); \
	})

extern void synchronize_rcu(void);

/*
 * Exchanges the pointer and waits for quiescent state.
 * The pointer returned can be freed.
 */
#define urcu_publish_content(p, v) \
	({ \
		void *oldptr; \
		oldptr = rcu_xchg_pointer(p, v); \
		synchronize_rcu(); \
		oldptr; \
	})

/*
 * Reader thread registration.
 */
extern void urcu_register_thread(void);
extern void urcu_unregister_thread(void);

#endif /* _URCU_H */
