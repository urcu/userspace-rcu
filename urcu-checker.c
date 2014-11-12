/*
 * urcu-checker.c
 *
 * Userspace RCU library checker
 *
 * Copyright (c) 2014 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 */

#include <string.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <urcu/urcu-checker.h>
#include <urcu/tls-compat.h>

#define URCU_DEBUG_STACK_LEN	10

struct urcu_debug_entry {
	void *ip;
	int depth;
};

struct urcu_debug_stack {
	struct urcu_debug_entry stack[URCU_DEBUG_STACK_LEN];
	int stackend;
};

static DEFINE_URCU_TLS(struct urcu_debug_stack, rcu_debug_stack);

void rcu_read_lock_debug(void)
{
	struct urcu_debug_stack *r = &URCU_TLS(rcu_debug_stack);

	r->stack[r->stackend++].ip = __builtin_return_address(0);
}

void rcu_read_unlock_debug(void)
{
	struct urcu_debug_stack *r = &URCU_TLS(rcu_debug_stack);

	assert(r->stackend != 0);
	r->stack[--r->stackend].ip = NULL;
}

void rcu_read_ongoing_check_debug(const char *func)
{
	struct urcu_debug_stack *r = &URCU_TLS(rcu_debug_stack);

	if (r->stackend == 0) {
		fprintf(stderr, "URCU LOCKED CHECK failure: %p\n",
			__builtin_return_address(0));
		abort();
	}
}
