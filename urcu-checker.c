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

/*
 * NOTE: build application with -rdynamic -ldl -lurcu-common.
 */

#define _GNU_SOURCE
#include <string.h>
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <execinfo.h>
#include <dlfcn.h>
#include <sys/types.h>
#include <urcu/urcu-checker.h>
#include <urcu/tls-compat.h>

#define URCU_DEBUG_STACK_LEN		10
#define DEFAULT_PRINT_BACKTRACE_LEN	5
#define BACKTRACE_LEN			16

#ifdef __linux__
#include <syscall.h>
#endif

#if defined(_syscall0)
_syscall0(pid_t, gettid)
#elif defined(__NR_gettid)
#include <unistd.h>
static inline pid_t gettid(void)
{
	return syscall(__NR_gettid);
}
#else
#include <sys/types.h>
#include <unistd.h>

/* Fall-back on getpid for tid if not available. */
static inline pid_t gettid(void)
{
	return getpid();
}
#endif

#define err_printf(fmt, args...) \
	fprintf(stderr, "[urcu-checker %ld/%ld] "  fmt, \
		(long) getpid(), (long) gettid(), ## args)

struct urcu_debug_entry {
	void *ip;
	int depth;
};

struct urcu_debug_stack {
	struct urcu_debug_entry stack[URCU_DEBUG_STACK_LEN];
	int stackend;
};

struct backtrace {
	void *ptrs[BACKTRACE_LEN];
	char **symbols;
};

static DEFINE_URCU_TLS(struct urcu_debug_stack, rcu_debug_stack);

static volatile int print_backtrace_len = DEFAULT_PRINT_BACKTRACE_LEN;

/*
 * Allocates a string, or NULL.
 */
static
char *get_symbol(const void *caller)
{
	Dl_info info;
	char *caller_symbol;

	if (caller && dladdr(caller, &info) && info.dli_sname) {
		caller_symbol = strdup(info.dli_sname);
	} else {
		caller_symbol = NULL;
	}
	return caller_symbol;
}

static inline __attribute__((always_inline))
void save_backtrace(struct backtrace *bt)
{
	memset(bt, 0, sizeof(*bt));
	(void) backtrace(bt->ptrs, BACKTRACE_LEN);
	bt->symbols = backtrace_symbols(bt->ptrs, BACKTRACE_LEN);
}

static
void free_backtrace(struct backtrace *bt)
{
	free(bt->symbols);
}

static
void print_bt(struct backtrace *bt)
{
	int j;
	unsigned int empty = 1;

	for (j = 0; j < BACKTRACE_LEN; j++) {
		if (bt->ptrs[j]) {
			empty = 0;
			break;
		}
	}
	if (empty)
		return;

	err_printf("[backtrace]\n");
	for (j = 0; j < BACKTRACE_LEN && j < print_backtrace_len; j++) {
		if (!bt->ptrs[j])
			continue;
		if (bt->symbols)
			err_printf(" %p <%s>\n", bt->ptrs[j], bt->symbols[j]);
		else
			err_printf(" %p\n", bt->ptrs[j]);
	}
}

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
		struct backtrace bt;

		err_printf("rcu_dereference() used outside of critical section at %p <%s>\n",
			__builtin_return_address(0),
			get_symbol(__builtin_return_address(0)));
		save_backtrace(&bt);
		print_bt(&bt);
		free_backtrace(&bt);
	}
}
