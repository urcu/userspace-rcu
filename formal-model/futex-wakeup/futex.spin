/*
 * futex.spin: Promela code to validate futex wakeup algorithm.
 *
 * Algorithm verified :
 *
 * queue = 0;
 * fut = 0;
 * runvar = 0;
 *
 *                            Waker
 *                            queue = 1;
 *                            if (fut == -1) {
 *                              fut = 0;
 *                            }
 *
 * Waiter
 * while (1) {
 *   progress:
 *   fut = fut - 1;
 *   if (queue == 1) {
 *     fut = 0;
 *   } else {
 *     if (fut == -1) {
 *        while (fut == -1) { }
 *     }
 *   }
 *   queue = 0;
 * }
 *
 * if queue = 1, then !_np
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

#define get_pid()       (_pid)

int queue[2] = 0;
int fut = 0;

active [2] proctype waker()
{
	assert(get_pid() < 2);

	queue[get_pid()] = 1;

	if
	:: (fut == -1) ->
		fut = 0;
	:: else ->
		skip;
	fi;

	queue[get_pid()] = 1;

	if
	:: (fut == -1) ->
		fut = 0;
	:: else ->
		skip;
	fi;

#ifdef INJ_QUEUE_NO_WAKE
	queue[get_pid()] = 1;
#endif
}


active proctype waiter()
{
	do
	:: 1 ->
#ifndef INJ_LATE_DEC
		fut = fut - 1;
#endif
		if
		:: (queue[0] == 1 || queue[1] == 1) ->
#ifndef INJ_LATE_DEC
			fut = 0;
#endif
			skip;
		:: else ->
#ifdef INJ_LATE_DEC
			fut = fut - 1;
#endif
			if
			:: (fut == -1) ->
				do
				:: 1 ->
					if
					:: (fut == -1) ->
						skip;
					:: else ->
						break;
					fi;
				od;
			:: else ->
				skip;
			fi;
		fi;
progress:
		if
		:: queue[0] == 1 ->
			queue[0] = 0;
		fi;
		if
		:: queue[1] == 1 ->
			queue[1] = 0;
		fi;
	od;
}
