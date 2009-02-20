/*
 * urcu.spin: Promela code to validate urcu.  See commit number
 *	3a9e6e9df706b8d39af94d2f027210e2e7d4106e of Mathieu Desnoyer's
 *      git archive at git://lttng.org/userspace-rcu.git
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
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 */

/* Promela validation variables. */

bit removed = 0;  /* Has RCU removal happened, e.g., list_del_rcu()? */
bit free = 0;     /* Has RCU reclamation happened, e.g., kfree()? */
bit need_mb = 0;  /* =1 says need reader mb, =0 for reader response. */
byte reader_progress[4];
		  /* Count of read-side statement executions. */
bit reader_done = 0;
		  /* =0 says reader still running, =1 says done. */
bit updater_done = 0;
		  /* =0 says updater still running, =1 says done. */

/* urcu definitions and variables, taken straight from the algorithm. */

#define RCU_GP_CTR_BIT (1 << 7)
#define RCU_GP_CTR_NEST_MASK (RCU_GP_CTR_BIT - 1)

byte urcu_gp_ctr = 1;
byte urcu_active_readers = 0;

/* Model the RCU read-side critical section. */

proctype urcu_reader()
{
	bit done = 0;
	bit mbok;
	byte tmp;
	byte tmp_removed;
	byte tmp_free;

	/* Absorb any early requests for memory barriers. */
	do
	:: need_mb == 1 ->
		need_mb = 0;
	:: !updater_done -> skip;
	:: 1 -> break;
	od;

	/*
	 * Each pass through this loop executes one read-side statement
	 * from the following code fragment:
	 *
	 *	rcu_read_lock(); [0a]
	 *	rcu_read_lock(); [0b]
	 *	p = rcu_dereference(global_p); [1]
	 *	x = p->data; [2]
	 *	rcu_read_unlock(); [3b]
	 *	rcu_read_unlock(); [3a]
	 *
	 * Because we are modeling a weak-memory machine, these statements
	 * can be seen in any order, the only restriction being that
	 * rcu_read_unlock() cannot precede the corresponding rcu_read_lock().
	 * The placement of the inner rcu_read_lock() and rcu_read_unlock()
	 * is non-deterministic, the above is but one possible placement.
	 * Intestingly enough, this model validates all possible placements
	 * of the inner rcu_read_lock() and rcu_read_unlock() statements,
	 * with the only constraint being that the rcu_read_lock() must
	 * precede the rcu_read_unlock().
	 *
	 * We also respond to memory-barrier requests, but only if our
	 * execution happens to be ordered.  If the current state is
	 * misordered, we ignore memory-barrier requests.
	 */
	do
	:: 1 ->
		if
		:: reader_progress[0] < 2 -> /* [0a and 0b] */
			tmp = urcu_active_readers;
			if
			:: (tmp & RCU_GP_CTR_NEST_MASK) == 0 ->
				tmp = urcu_gp_ctr;
				do
				:: (reader_progress[1] +
				    reader_progress[2] +
				    reader_progress[3] == 0) && need_mb == 1 ->
					need_mb = 0;
				:: !updater_done -> skip;
				:: 1 -> break;
				od;
				urcu_active_readers = tmp;
			 :: else ->
				urcu_active_readers = tmp + 1;
			fi;
			reader_progress[0] = reader_progress[0] + 1;
		:: reader_progress[1] == 0 -> /* [1] */
			tmp_removed = removed;
			reader_progress[1] = 1;
		:: reader_progress[2] == 0 -> /* [2] */
			tmp_free = free;
			reader_progress[2] = 1;
		:: ((reader_progress[0] > reader_progress[3]) &&
		    (reader_progress[3] < 2)) -> /* [3a and 3b] */
			tmp = urcu_active_readers - 1;
			urcu_active_readers = tmp;
			reader_progress[3] = reader_progress[3] + 1;
		:: else -> break;
		fi;

		/* Process memory-barrier requests, if it is safe to do so. */
		atomic {
			mbok = 0;
			tmp = 0;
			do
			:: tmp < 4 && reader_progress[tmp] == 0 ->
				tmp = tmp + 1;
				break;
			:: tmp < 4 && reader_progress[tmp] != 0 ->
				tmp = tmp + 1;
			:: tmp >= 4 &&
			   reader_progress[0] == reader_progress[3] ->
				done = 1;
				break;
			:: tmp >= 4 &&
			   reader_progress[0] != reader_progress[3] ->
			   	break;
			od;
			do
			:: tmp < 4 && reader_progress[tmp] == 0 ->
				tmp = tmp + 1;
			:: tmp < 4 && reader_progress[tmp] != 0 ->
				break;
			:: tmp >= 4 ->
				mbok = 1;
				break;
			od

		}

		if
		:: mbok == 1 ->
			/* We get here if mb processing is safe. */
			do
			:: need_mb == 1 ->
				need_mb = 0;
			:: !updater_done -> skip;
			:: 1 -> break;
			od;
		:: else -> skip;
		fi;

		/*
		 * Check to see if we have modeled the entire RCU read-side
		 * critical section, and leave if so.
		 */
		if
		:: done == 1 -> break;
		:: else -> skip;
		fi
	od;
	assert((tmp_free == 0) || (tmp_removed == 1));

	/* Reader has completed. */
	reader_done = 1;

	/* Process any late-arriving memory-barrier requests. */
	do
	:: need_mb == 1 ->
		need_mb = 0;
	:: !updater_done -> skip;
	:: 1 -> break;
	od;
}

/* Model the RCU update process. */

proctype urcu_updater()
{
	/* prior synchronize_rcu(), second counter flip. */
	need_mb = 1;
	do
	:: need_mb == 1 -> skip;
	:: need_mb == 0 -> break;
	od;
	urcu_gp_ctr = urcu_gp_ctr + RCU_GP_CTR_BIT;
	need_mb = 1;
	do
	:: need_mb == 1 -> skip;
	:: need_mb == 0 -> break;
	od;
	do
	:: 1 ->
		if
		:: (urcu_active_readers & RCU_GP_CTR_NEST_MASK) != 0 &&
		   (urcu_active_readers & ~RCU_GP_CTR_NEST_MASK) !=
		   (urcu_gp_ctr & ~RCU_GP_CTR_NEST_MASK) ->
			skip;
		:: else -> break;
		fi;
	od;
	need_mb = 1;
	do
	:: need_mb == 1 -> skip;
	:: need_mb == 0 -> break;
	od;

	/* Removal statement, e.g., list_del_rcu(). */
	removed = 1;

	/* current synchronize_rcu(), first counter flip. */
	need_mb = 1;
	do
	:: need_mb == 1 -> skip;
	:: need_mb == 0 -> break;
	od;
	urcu_gp_ctr = urcu_gp_ctr + RCU_GP_CTR_BIT;
	need_mb = 1;
	do
	:: need_mb == 1 -> skip;
	:: need_mb == 0 -> break;
	od;
	do
	:: 1 ->
		if
		:: (urcu_active_readers & RCU_GP_CTR_NEST_MASK) != 0 &&
		   (urcu_active_readers & ~RCU_GP_CTR_NEST_MASK) !=
		   (urcu_gp_ctr & ~RCU_GP_CTR_NEST_MASK) ->
			skip;
		:: else -> break;
		fi;
	od;
	need_mb = 1;
	do
	:: need_mb == 1 -> skip;
	:: need_mb == 0 -> break;
	od;

	/* current synchronize_rcu(), second counter flip. */
	need_mb = 1;
	do
	:: need_mb == 1 -> skip;
	:: need_mb == 0 -> break;
	od;
	urcu_gp_ctr = urcu_gp_ctr + RCU_GP_CTR_BIT;
	need_mb = 1;
	do
	:: need_mb == 1 -> skip;
	:: need_mb == 0 -> break;
	od;
	do
	:: 1 ->
		if
		:: (urcu_active_readers & RCU_GP_CTR_NEST_MASK) != 0 &&
		   (urcu_active_readers & ~RCU_GP_CTR_NEST_MASK) !=
		   (urcu_gp_ctr & ~RCU_GP_CTR_NEST_MASK) ->
			skip;
		:: else -> break;
		fi;
	od;
	need_mb = 1;
	do
	:: need_mb == 1 -> skip;
	:: need_mb == 0 -> break;
	od;

	/* free-up step, e.g., kfree(). */
	free = 1;

	/*
	 * Signal updater done, ending any otherwise-infinite loops
	 * in the reading process.
	 */
	updater_done = 1;
}

/*
 * Initialize the array, spawn a reader and an updater.  Because readers
 * are independent of each other, only one reader is needed.
 */

init {
	atomic {
		reader_progress[0] = 0;
		reader_progress[1] = 0;
		reader_progress[2] = 0;
		reader_progress[3] = 0;
		run urcu_reader();
		run urcu_updater();
	}
}
