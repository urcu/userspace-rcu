/*
 * mem.spin: Promela code to validate memory barriers with OOO memory.
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
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
 *
 * Copyright (c) 2009 Mathieu Desnoyers
 */

/* Promela validation variables. */

#define NR_READERS 1
#define NR_WRITERS 1

#define NR_PROCS 2

#define get_pid()	(_pid)

/*
 * Each process have its own data in cache. Caches are randomly updated.
 * smp_wmb and smp_rmb forces cache updates (write and read), wmb_mb forces
 * both.
 */

#define DECLARE_CACHED_VAR(type, x, v)	\
	type mem_##x = v;		\
	type cached_##x[NR_PROCS] = v;	\
	bit cache_dirty_##x[NR_PROCS] = 0

#define IS_CACHE_DIRTY(x, id)	(cache_dirty_##x[id])

#define READ_CACHED_VAR(x)	(cached_##x[get_pid()])

#define WRITE_CACHED_VAR(x, v)		\
	atomic {			\
		cached_##x[get_pid()] = v;	\
		cache_dirty_##x[get_pid()] = 1;	\
	}

#define CACHE_WRITE_TO_MEM(x, id)		\
	if					\
	:: IS_CACHE_DIRTY(x, id) ->		\
		mem_##x = cached_##x[id];	\
		cache_dirty_##x[id] = 0;	\
	:: else ->				\
		skip				\
	fi;

#define CACHE_READ_FROM_MEM(x, id)	\
	if				\
	:: !IS_CACHE_DIRTY(x, id) ->	\
		cached_##x[id] = mem_##x;\
	:: else ->			\
		skip			\
	fi;

/*
 * May update other caches if cache is dirty, or not.
 */
#define RANDOM_CACHE_WRITE_TO_MEM(x, id)\
	if				\
	:: 1 -> CACHE_WRITE_TO_MEM(x, id);	\
	:: 1 -> skip			\
	fi;

#define RANDOM_CACHE_READ_FROM_MEM(x, id)\
	if				\
	:: 1 -> CACHE_READ_FROM_MEM(x, id);	\
	:: 1 -> skip			\
	fi;

inline smp_rmb()
{
	atomic {
		CACHE_READ_FROM_MEM(alpha, get_pid());
		CACHE_READ_FROM_MEM(beta, get_pid());
	}
}

inline smp_wmb()
{
	atomic {
		CACHE_WRITE_TO_MEM(alpha, get_pid());
		CACHE_WRITE_TO_MEM(beta, get_pid());
	}
}

inline smp_mb()
{
	atomic {
		smp_wmb();
		smp_rmb();
	}
}

/*
 * Instruction scheduling support. Declares instruction data flow dependency.
 * INSTRUCTION_SCHED_BEGIN/INSTRUCTION_SCHED_END can be nested.
 */
#define INSTRUCTION_SCHED_BEGIN(i)	\
	if				\
	:: 1 ->				\
		ooo_mem(i)

/* No data flow dependency between two consecutive instructions */
#define INSTRUCTION_SCHED_NODEP_NEXT(i)	\
	:: 1 ->				\
		ooo_mem(i)

/* Has dependency between two consecutive instructions */
#define INSTRUCTION_SCHED_DEP_NEXT(i)	\
		ooo_mem(i)

#define INSTRUCTION_SCHED_END(i)	\
	fi

inline ooo_mem()
{
	atomic {
		RANDOM_CACHE_WRITE_TO_MEM(alpha, get_pid());
		RANDOM_CACHE_WRITE_TO_MEM(beta, get_pid());
		RANDOM_CACHE_READ_FROM_MEM(alpha, get_pid());
		RANDOM_CACHE_READ_FROM_MEM(beta, get_pid());
	}
}

/* Keep in sync manually with smp_rmb, wmp_wmb and ooo_mem */
DECLARE_CACHED_VAR(byte, alpha, 0);
DECLARE_CACHED_VAR(byte, beta, 0);

/* value 2 is uninitialized */
byte read_one = 2;
byte read_two = 2;

active proctype test_proc_one()
{
	assert(get_pid() < NR_PROCS);

	INSTRUCTION_SCHED_BEGIN();
	WRITE_CACHED_VAR(alpha, 1);
	INSTRUCTION_SCHED_DEP_NEXT();
	smp_wmb();
#ifndef USE_SYNC_CORE
	INSTRUCTION_SCHED_NODEP_NEXT();
#else
	// if we use a sync_core(); (equivalent to smp_mb())
	INSTRUCTION_SCHED_DEP_NEXT();
#endif
	smp_rmb();
	INSTRUCTION_SCHED_DEP_NEXT();
	read_one = READ_CACHED_VAR(beta);
	INSTRUCTION_SCHED_END();

	// test : [] (read_one == 0 -> read_two != 0)
	// test : [] (read_two == 0 -> read_one != 0)
	assert(!(read_one == 0 && read_two == 0));
}

active proctype test_proc_two()
{
	assert(get_pid() < NR_PROCS);

	INSTRUCTION_SCHED_BEGIN();
	WRITE_CACHED_VAR(beta, 1);
	INSTRUCTION_SCHED_DEP_NEXT();
	smp_wmb();
#ifndef USE_SYNC_CORE
	INSTRUCTION_SCHED_NODEP_NEXT();
#else
	// if we use a sync_core(); (equivalent to smp_mb())
	// INSTRUCTION_SCHED_DEP_NEXT();
#endif
	smp_rmb();
	INSTRUCTION_SCHED_DEP_NEXT();
	read_two = READ_CACHED_VAR(alpha);
	INSTRUCTION_SCHED_END();

	// test : [] (read_one == 0 -> read_two != 0)
	// test : [] (read_two == 0 -> read_one != 0)
	assert(!(read_one == 0 && read_two == 0));
}
