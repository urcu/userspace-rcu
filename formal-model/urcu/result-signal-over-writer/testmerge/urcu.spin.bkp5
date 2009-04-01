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
 * smp_wmb and smp_rmb forces cache updates (write and read), smp_mb forces
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

/*
 * Remote barriers tests the scheme where a signal (or IPI) is sent to all
 * reader threads to promote their compiler barrier to a smp_mb().
 */
#ifdef REMOTE_BARRIERS

inline smp_rmb_pid(i)
{
	atomic {
		CACHE_READ_FROM_MEM(urcu_gp_ctr, i);
		CACHE_READ_FROM_MEM(urcu_active_readers_one, i);
		CACHE_READ_FROM_MEM(generation_ptr, i);
	}
}

inline smp_wmb_pid(i)
{
	atomic {
		CACHE_WRITE_TO_MEM(urcu_gp_ctr, i);
		CACHE_WRITE_TO_MEM(urcu_active_readers_one, i);
		CACHE_WRITE_TO_MEM(generation_ptr, i);
	}
}

inline smp_mb_pid(i)
{
	atomic {
#ifndef NO_WMB
		smp_wmb_pid(i);
#endif
#ifndef NO_RMB
		smp_rmb_pid(i);
#endif
#ifdef NO_WMB
#ifdef NO_RMB
		ooo_mem(i);
#endif
#endif
	}
}

/*
 * Readers do a simple barrier(), writers are doing a smp_mb() _and_ sending a
 * signal or IPI to have all readers execute a smp_mb.
 * We are not modeling the whole rendez-vous between readers and writers here,
 * we just let the writer update each reader's caches remotely.
 */
inline smp_mb(i)
{
	if
	:: get_pid() >= NR_READERS ->
		smp_mb_pid(get_pid());
		i = 0;
		do
		:: i < NR_READERS ->
			smp_mb_pid(i);
			i++;
		:: i >= NR_READERS -> break
		od;
		smp_mb_pid(get_pid());
	:: else -> skip;
	fi;
}

#else

inline smp_rmb(i)
{
	atomic {
		CACHE_READ_FROM_MEM(urcu_gp_ctr, get_pid());
		CACHE_READ_FROM_MEM(urcu_active_readers_one, get_pid());
		CACHE_READ_FROM_MEM(generation_ptr, get_pid());
	}
}

inline smp_wmb(i)
{
	atomic {
		CACHE_WRITE_TO_MEM(urcu_gp_ctr, get_pid());
		CACHE_WRITE_TO_MEM(urcu_active_readers_one, get_pid());
		CACHE_WRITE_TO_MEM(generation_ptr, get_pid());
	}
}

inline smp_mb(i)
{
	atomic {
#ifndef NO_WMB
		smp_wmb(i);
#endif
#ifndef NO_RMB
		smp_rmb(i);
#endif
#ifdef NO_WMB
#ifdef NO_RMB
		ooo_mem(i);
#endif
#endif
	}
}

#endif

/* Keep in sync manually with smp_rmb, wmp_wmb and ooo_mem */
DECLARE_CACHED_VAR(byte, urcu_gp_ctr, 1);
/* Note ! currently only one reader */
DECLARE_CACHED_VAR(byte, urcu_active_readers_one, 0);
/* pointer generation */
DECLARE_CACHED_VAR(byte, generation_ptr, 0);

byte last_free_gen = 0;
bit free_done = 0;
byte read_generation = 1;
bit data_access = 0;

bit write_lock = 0;

inline ooo_mem(i)
{
	atomic {
		RANDOM_CACHE_WRITE_TO_MEM(urcu_gp_ctr, get_pid());
		RANDOM_CACHE_WRITE_TO_MEM(urcu_active_readers_one,
						get_pid());
		RANDOM_CACHE_WRITE_TO_MEM(generation_ptr, get_pid());
		RANDOM_CACHE_READ_FROM_MEM(urcu_gp_ctr, get_pid());
		RANDOM_CACHE_READ_FROM_MEM(urcu_active_readers_one,
						get_pid());
		RANDOM_CACHE_READ_FROM_MEM(generation_ptr, get_pid());
	}
}

#define get_readerid()	(get_pid())
#define get_writerid()	(get_readerid() + NR_READERS)

inline wait_for_reader(tmp, id, i)
{
	do
	:: 1 ->
		tmp = READ_CACHED_VAR(urcu_active_readers_one);
		ooo_mem(i);
		if
		:: (tmp & RCU_GP_CTR_NEST_MASK)
			&& ((tmp ^ READ_CACHED_VAR(urcu_gp_ctr))
				& RCU_GP_CTR_BIT) ->
#ifndef GEN_ERROR_WRITER_PROGRESS
			smp_mb(i);
#else
			ooo_mem(i);
#endif
		:: else	->
			break;
		fi;
	od;
}

inline wait_for_quiescent_state(tmp, i, j)
{
	i = 0;
	do
	:: i < NR_READERS ->
		wait_for_reader(tmp, i, j);
		if
		:: (NR_READERS > 1) && (i < NR_READERS - 1)
			-> ooo_mem(j);
		:: else
			-> skip;
		fi;
		i++
	:: i >= NR_READERS -> break
	od;
}

/* Model the RCU read-side critical section. */

inline urcu_one_read(i, nest_i, tmp, tmp2)
{
	nest_i = 0;
	do
	:: nest_i < READER_NEST_LEVEL ->
		ooo_mem(i);
		tmp = READ_CACHED_VAR(urcu_active_readers_one);
		ooo_mem(i);
		if
		:: (!(tmp & RCU_GP_CTR_NEST_MASK))
			->
			tmp2 = READ_CACHED_VAR(urcu_gp_ctr);
			ooo_mem(i);
			WRITE_CACHED_VAR(urcu_active_readers_one, tmp2);
		:: else	->
			WRITE_CACHED_VAR(urcu_active_readers_one,
					 tmp + 1);
		fi;
		smp_mb(i);
		nest_i++;
	:: nest_i >= READER_NEST_LEVEL -> break;
	od;

	ooo_mem(i);
	read_generation = READ_CACHED_VAR(generation_ptr);
	ooo_mem(i);
	data_access = 1;
	ooo_mem(i);
	data_access = 0;

	nest_i = 0;
	do
	:: nest_i < READER_NEST_LEVEL ->
		smp_mb(i);
		tmp2 = READ_CACHED_VAR(urcu_active_readers_one);
		ooo_mem(i);
		WRITE_CACHED_VAR(urcu_active_readers_one, tmp2 - 1);
		nest_i++;
	:: nest_i >= READER_NEST_LEVEL -> break;
	od;
	ooo_mem(i);
	//smp_mc(i);	/* added */
}

active [NR_READERS] proctype urcu_reader()
{
	byte i, nest_i;
	byte tmp, tmp2;

	assert(get_pid() < NR_PROCS);

end_reader:
	do
	:: 1 ->
		/*
		 * We do not test reader's progress here, because we are mainly
		 * interested in writer's progress. The reader never blocks
		 * anyway. We have to test for reader/writer's progress
		 * separately, otherwise we could think the writer is doing
		 * progress when it's blocked by an always progressing reader.
		 */
#ifdef READER_PROGRESS
progress_reader:
#endif
		urcu_one_read(i, nest_i, tmp, tmp2);
	od;
}

/* Model the RCU update process. */

active [NR_WRITERS] proctype urcu_writer()
{
	byte i, j;
	byte tmp;
	byte old_gen;

	assert(get_pid() < NR_PROCS);

	do
	:: (READ_CACHED_VAR(generation_ptr) < 5) ->
#ifdef WRITER_PROGRESS
progress_writer1:
#endif
		ooo_mem(i);
		atomic {
			old_gen = READ_CACHED_VAR(generation_ptr);
			WRITE_CACHED_VAR(generation_ptr, old_gen + 1);
		}
		ooo_mem(i);

		do
		:: 1 ->
			atomic {
				if
				:: write_lock == 0 ->
					write_lock = 1;
					break;
				:: else ->
					skip;
				fi;
			}
		od;
		smp_mb(i);
		tmp = READ_CACHED_VAR(urcu_gp_ctr);
		ooo_mem(i);
		WRITE_CACHED_VAR(urcu_gp_ctr, tmp ^ RCU_GP_CTR_BIT);
		ooo_mem(i);
		//smp_mc(i);
		wait_for_quiescent_state(tmp, i, j);
		//smp_mc(i);
#ifndef SINGLE_FLIP
		ooo_mem(i);
		tmp = READ_CACHED_VAR(urcu_gp_ctr);
		ooo_mem(i);
		WRITE_CACHED_VAR(urcu_gp_ctr, tmp ^ RCU_GP_CTR_BIT);
		//smp_mc(i);
		ooo_mem(i);
		wait_for_quiescent_state(tmp, i, j);
#endif
		smp_mb(i);
		write_lock = 0;
		/* free-up step, e.g., kfree(). */
		atomic {
			last_free_gen = old_gen;
			free_done = 1;
		}
	:: else -> break;
	od;
	/*
	 * Given the reader loops infinitely, let the writer also busy-loop
	 * with progress here so, with weak fairness, we can test the
	 * writer's progress.
	 */
end_writer:
	do
	:: 1 ->
#ifdef WRITER_PROGRESS
progress_writer2:
#endif
		skip;
	od;
}
