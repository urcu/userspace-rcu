#ifndef _URCU_H
#define _URCU_H

/* The "volatile" is due to gcc bugs */
#define barrier() __asm__ __volatile__("": : :"memory")

/* x86 32/64 specific */
#define mb()    asm volatile("mfence":::"memory")
#define rmb()   asm volatile("lfence":::"memory")
#define wmb()   asm volatile("sfence" ::: "memory")



/* x86 32 */
static inline void atomic_inc(int *v)
{
	asm volatile("lock; incl %0"
		     : "+m" (v->counter));
}

/* Nop everywhere except on alpha. */
#define smp_read_barrier_depends()

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

extern void *urcu_publish_content(void **ptr, void *new);

/*
 * Reader thread registration.
 */
extern void urcu_register_thread(void);
extern void urcu_register_thread(void);

#endif /* _URCU_H */
