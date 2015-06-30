/*
 * test_uatomic.c
 *
 * Userspace RCU library - test atomic operations
 *
 * Copyright February 2009 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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
 * You should have received a copy of the GNU General Public License along
 * with this program; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */

#include <stdio.h>
#include <urcu/uatomic.h>

#include "tap.h"

#define NR_TESTS 17

struct testvals {
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	unsigned char c;
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	unsigned short s;
#endif
	unsigned int i;
	unsigned long l;
};

static struct testvals vals;

#define do_test(ptr)				\
do {						\
	__typeof__(*(ptr)) v;			\
						\
	uatomic_add(ptr, 10);			\
	ok1(uatomic_read(ptr) == 10);	\
						\
	uatomic_add(ptr, -11UL);		\
	ok1(uatomic_read(ptr) == (__typeof__(*(ptr)))-1UL);	\
						\
	v = uatomic_cmpxchg(ptr, -1UL, 22);	\
	ok1(uatomic_read(ptr) == 22);	\
	ok1(v == (__typeof__(*(ptr)))-1UL);	\
						\
	v = uatomic_cmpxchg(ptr, 33, 44);	\
	ok1(uatomic_read(ptr) == 22);	\
	ok1(v == 22);			\
						\
	v = uatomic_xchg(ptr, 55);		\
	ok1(uatomic_read(ptr) == 55);	\
	ok1(v == 22);			\
						\
	uatomic_set(ptr, 22);			\
	uatomic_inc(ptr);			\
	ok1(uatomic_read(ptr) == 23);	\
						\
	uatomic_dec(ptr);			\
	ok1(uatomic_read(ptr) == 22);	\
						\
	v = uatomic_add_return(ptr, 74);	\
	ok1(v == 96);			\
	ok1(uatomic_read(ptr) == 96);	\
						\
	uatomic_or(ptr, 58);			\
	ok1(uatomic_read(ptr) == 122);	\
						\
	v = uatomic_sub_return(ptr, 1);		\
	ok1(v == 121);			\
						\
	uatomic_sub(ptr, (unsigned int) 2);	\
	ok1(uatomic_read(ptr) == 119);	\
						\
	uatomic_inc(ptr);			\
	uatomic_inc(ptr);			\
	ok1(uatomic_read(ptr) == 121);	\
						\
	uatomic_and(ptr, 129);			\
	ok1(uatomic_read(ptr) == 1);	\
						\
} while (0)

int main(int argc, char **argv)
{
	int nr_run = 2;
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	nr_run += 1;
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	nr_run += 1;
#endif

	plan_tests(nr_run * NR_TESTS);
#ifdef UATOMIC_HAS_ATOMIC_BYTE
	diag("Test atomic ops on byte");
	do_test(&vals.c);
#endif
#ifdef UATOMIC_HAS_ATOMIC_SHORT
	diag("Test atomic ops on short");
	do_test(&vals.s);
#endif
	diag("Test atomic ops on int");
	do_test(&vals.i);
	diag("Test atomic ops on long");
	do_test(&vals.l);

	return exit_status();
}
