/*
 * mem.spin: Promela code to validate memory barriers with out-of-order memory
 * and out-of-order instruction scheduling.
 *
 * Algorithm verified :
 *
 * alpha = 0;
 * beta = 0;
 * x = 1;
 * y = 1;
 *
 * Process A                  Process B
 * alpha = 1;                 beta = 1;
 * mb();                      mb();
 * x = beta;                  y = alpha;
 *
 * if x = 0, then y != 0
 * if y = 0, then x != 0
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

/*
 * Produced process control and data flow. Updated after each instruction to
 * show which variables are ready. Using one-hot bit encoding per variable to
 * save state space. Used as triggers to execute the instructions having those
 * variables as input. Leaving bits active to inhibit instruction execution.
 * Scheme used to make instruction disabling and automatic dependency fall-back
 * automatic.
 */

#define CONSUME_TOKENS(state, bits, notbits)			\
	((!(state & (notbits))) && (state & (bits)) == (bits))

#define PRODUCE_TOKENS(state, bits)				\
	state = state | (bits);

#define CLEAR_TOKENS(state, bits)				\
	state = state & ~(bits)

#define NR_PROCS 2

#define get_pid()	(_pid)

/*
 * Each process have its own data in cache. Caches are randomly updated.
 * smp_wmb and smp_rmb forces cache updates (write and read), wmb_mb forces
 * both.
 */

#define DECLARE_CACHED_VAR(type, x, v)		\
	type mem_##x = v;			\
	type cached_##x[NR_PROCS] = v;		\
	bit cache_dirty_##x[NR_PROCS] = 0;

#define IS_CACHE_DIRTY(x, id)	(cache_dirty_##x[id])

#define READ_CACHED_VAR(x)			\
	(cached_##x[get_pid()])

#define WRITE_CACHED_VAR(x, v)			\
	atomic {				\
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

#define CACHE_READ_FROM_MEM(x, id)		\
	if					\
	:: !IS_CACHE_DIRTY(x, id) ->		\
		cached_##x[id] = mem_##x;	\
	:: else ->				\
		skip				\
	fi;

/*
 * May update other caches if cache is dirty, or not.
 */
#define RANDOM_CACHE_WRITE_TO_MEM(x, id)	\
	if					\
	:: 1 -> CACHE_WRITE_TO_MEM(x, id);	\
	:: 1 -> skip				\
	fi;

#define RANDOM_CACHE_READ_FROM_MEM(x, id)\
	if					\
	:: 1 -> CACHE_READ_FROM_MEM(x, id);	\
	:: 1 -> skip				\
	fi;

inline ooo_mem()
{
	atomic {
		RANDOM_CACHE_WRITE_TO_MEM(alpha, get_pid());
		RANDOM_CACHE_WRITE_TO_MEM(beta, get_pid());
		RANDOM_CACHE_READ_FROM_MEM(alpha, get_pid());
		RANDOM_CACHE_READ_FROM_MEM(beta, get_pid());
	}
}

/* must consume all prior read tokens */
inline smp_rmb()
{
	atomic {
		/* todo : consume all read tokens .. ? */
		CACHE_READ_FROM_MEM(alpha, get_pid());
		CACHE_READ_FROM_MEM(beta, get_pid());
	}
}

/* must consume all prior write tokens */
inline smp_wmb()
{
	atomic {
		CACHE_WRITE_TO_MEM(alpha, get_pid());
		CACHE_WRITE_TO_MEM(beta, get_pid());
	}
}

/* sync_core() must consume all prior read and write tokens, including rmb/wmb
 * tokens */

/* must consume all prior read and write tokens */
inline smp_mb()
{
	atomic {
		smp_wmb();
		/* sync_core() */
		smp_rmb();
	}
}

/* Keep in sync manually with smp_rmb, wmp_wmb and ooo_mem */
DECLARE_CACHED_VAR(byte, alpha, 0);
DECLARE_CACHED_VAR(byte, beta, 0);

byte read_one = 1;
byte read_two = 1;

/*
 * Bit encoding, proc_one_produced :
 */

#define P1_PROD_NONE	(1 << 0)

#define P1_WRITE	(1 << 1)
#define P1_WMB		(1 << 2)
#define P1_SYNC_CORE	(1 << 3)
#define P1_RMB		(1 << 4)
#define P1_READ		(1 << 5)

int proc_one_produced;

active proctype test_proc_one()
{
	assert(get_pid() < NR_PROCS);

	PRODUCE_TOKENS(proc_one_produced, P1_PROD_NONE);

#ifdef NO_WMB
	PRODUCE_TOKENS(proc_one_produced, P1_WMB);
#endif
#ifdef NO_RMB
	PRODUCE_TOKENS(proc_one_produced, P1_RMB);
#endif
#ifdef NO_SYNC
	PRODUCE_TOKENS(proc_one_produced, P1_SYNC_CORE);
#endif

	do
	:: CONSUME_TOKENS(proc_one_produced, P1_PROD_NONE, P1_WRITE) ->
		ooo_mem();
		WRITE_CACHED_VAR(alpha, 1);
		ooo_mem();
		PRODUCE_TOKENS(proc_one_produced, P1_WRITE);
	:: CONSUME_TOKENS(proc_one_produced, P1_WRITE, P1_WMB) ->
		smp_wmb();
		PRODUCE_TOKENS(proc_one_produced, P1_WMB);
	:: CONSUME_TOKENS(proc_one_produced, P1_WRITE | P1_WMB, P1_SYNC_CORE) ->
		/* sync_core(); */
		PRODUCE_TOKENS(proc_one_produced, P1_SYNC_CORE);
	:: CONSUME_TOKENS(proc_one_produced, P1_SYNC_CORE, P1_RMB) ->
		smp_rmb();
		PRODUCE_TOKENS(proc_one_produced, P1_RMB);
	:: CONSUME_TOKENS(proc_one_produced, P1_RMB | P1_SYNC_CORE, P1_READ) ->
		ooo_mem();
		read_one = READ_CACHED_VAR(beta);
		ooo_mem();
		PRODUCE_TOKENS(proc_one_produced, P1_READ);
	:: CONSUME_TOKENS(proc_one_produced, P1_PROD_NONE | P1_WRITE
		| P1_WMB | P1_SYNC_CORE | P1_RMB | P1_READ, 0) ->
		break;
	od;

	//CLEAR_TOKENS(proc_one_produced,
	//	P1_PROD_NONE | P1_WRITE | P1_WMB | P1_SYNC_CORE | P1_RMB |
	//	P2_READ);

	// test : [] (read_one == 0 -> read_two != 0)
	// test : [] (read_two == 0 -> read_one != 0)
	assert(!(read_one == 0 && read_two == 0));
}


/*
 * Bit encoding, proc_two_produced :
 */

#define P2_PROD_NONE	(1 << 0)

#define P2_WRITE	(1 << 1)
#define P2_WMB		(1 << 2)
#define P2_SYNC_CORE	(1 << 3)
#define P2_RMB		(1 << 4)
#define P2_READ		(1 << 5)

int proc_two_produced;

active proctype test_proc_two()
{
	assert(get_pid() < NR_PROCS);

	PRODUCE_TOKENS(proc_two_produced, P2_PROD_NONE);

#ifdef NO_WMB
	PRODUCE_TOKENS(proc_two_produced, P2_WMB);
#endif
#ifdef NO_RMB
	PRODUCE_TOKENS(proc_two_produced, P2_RMB);
#endif
#ifdef NO_SYNC
	PRODUCE_TOKENS(proc_two_produced, P2_SYNC_CORE);
#endif

	do
	:: CONSUME_TOKENS(proc_two_produced, P2_PROD_NONE, P2_WRITE) ->
		ooo_mem();
		WRITE_CACHED_VAR(beta, 1);
		ooo_mem();
		PRODUCE_TOKENS(proc_two_produced, P2_WRITE);
	:: CONSUME_TOKENS(proc_two_produced, P2_WRITE, P2_WMB) ->
		smp_wmb();
		PRODUCE_TOKENS(proc_two_produced, P2_WMB);
	:: CONSUME_TOKENS(proc_two_produced, P2_WRITE | P2_WMB, P2_SYNC_CORE) ->
		/* sync_core(); */
		PRODUCE_TOKENS(proc_two_produced, P2_SYNC_CORE);
	:: CONSUME_TOKENS(proc_two_produced, P2_SYNC_CORE, P2_RMB) ->
		smp_rmb();
		PRODUCE_TOKENS(proc_two_produced, P2_RMB);
	:: CONSUME_TOKENS(proc_two_produced, P2_SYNC_CORE | P2_RMB, P2_READ) ->
		ooo_mem();
		read_two = READ_CACHED_VAR(alpha);
		ooo_mem();
		PRODUCE_TOKENS(proc_two_produced, P2_READ);
	:: CONSUME_TOKENS(proc_two_produced, P2_PROD_NONE | P2_WRITE
		| P2_WMB | P2_SYNC_CORE | P2_RMB | P2_READ, 0) ->
		break;
	od;

	//CLEAR_TOKENS(proc_two_produced,
	//	P2_PROD_NONE | P2_WRITE | P2_WMB | P2_SYNC_CORE | P2_RMB |
	//	P2_READ);

	// test : [] (read_one == 0 -> read_two != 0)
	// test : [] (read_two == 0 -> read_one != 0)
	assert(!(read_one == 0 && read_two == 0));
}
