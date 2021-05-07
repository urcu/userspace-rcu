/*
 * test_arch.c
 *
 * Userspace RCU library - test arch headers
 *
 * Copyright February 2021 Michael Jeanson <mjeanson@efficios.com>
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
#include <urcu/arch.h>

#include "tap.h"

#define NR_TESTS 1


/*
 * This is only to make sure the static inline caa_get_cycles() in the public
 * headers builds properly.
 */
static
void test_caa_get_cycles(void) {
	caa_cycles_t cycles = 0;


	cycles = caa_get_cycles();

	ok(cycles != 0, "caa_get_cycles works");
}

int main(void)
{
	plan_tests(NR_TESTS);

	test_caa_get_cycles();

	return exit_status();
}
