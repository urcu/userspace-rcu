/*
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

/* 16 CPUs max (byte has 8 bits, divided in two) */

#ifndef CONFIG_BITS_PER_BYTE
#define BITS_PER_BYTE		8
#else
#define BITS_PER_BYTE		CONFIG_BITS_PER_BYTE
#endif

#define HBPB			(BITS_PER_BYTE / 2)	/* 4 */
#define HMASK			((1 << HBPB) - 1)	/* 0x0F */

/* for byte type */
#define LOW_HALF(val)		((val) & HMASK)
#define LOW_HALF_INC		1

#define HIGH_HALF(val)		((val) & (HMASK << HBPB))
#define HIGH_HALF_INC		(1 << HBPB)

byte lock = 0;
byte refcount = 0;

inline spin_lock(lock, ticket)
{
	atomic {
		ticket = HIGH_HALF(lock) >> HBPB;
		lock = lock + HIGH_HALF_INC;	/* overflow expected */
	}

	do
	:: 1 ->
		if
		:: (LOW_HALF(lock) == ticket) ->
			break;
		:: else ->
			skip;
		fi;
	od;
}

inline spin_unlock(lock)
{
	lock = HIGH_HALF(lock) | LOW_HALF(lock + LOW_HALF_INC);
}

proctype proc_X()
{
	byte ticket;

	do
	:: 1->
		spin_lock(lock, ticket);
		refcount = refcount + 1;
		refcount = refcount - 1;
		spin_unlock(lock);
	od;
}

init
{
	run proc_X();
	run proc_X();
	run proc_X();
	run proc_X();
	run proc_X();
}
