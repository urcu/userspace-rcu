/*
 * Copyright 2021 Simon Marchi <simon.marchi@efficios.com>
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

/*
 * This file is meant to verify that headers are compatible with both C and
 * C++.  It includes all exported headers and is compiled as C and C++ source.
 */

#ifndef DYNAMIC_LINK_TEST
# define _LGPL_SOURCE
#endif

#include <urcu/arch.h>
#include <urcu/call-rcu.h>
#include <urcu/cds.h>
#include <urcu/compiler.h>
#include <urcu/debug.h>
#include <urcu/defer.h>
#include <urcu/flavor.h>
#include <urcu/futex.h>
#include <urcu/hlist.h>
#include <urcu/lfstack.h>
#include <urcu/list.h>
#include <urcu/pointer.h>
#include <urcu/rcuhlist.h>
#include <urcu/rculfhash.h>
#include <urcu/rculfqueue.h>
#include <urcu/rculfstack.h>
#include <urcu/rculist.h>
#include <urcu/ref.h>
#include <urcu/syscall-compat.h>
#include <urcu/system.h>
#include <urcu/tls-compat.h>
#include <urcu/uatomic.h>
#include <urcu/urcu-bp.h>
#include <urcu/urcu.h>
#include <urcu/urcu-mb.h>
#include <urcu/urcu-memb.h>
#include <urcu/urcu-qsbr.h>
#include <urcu/urcu-signal.h>
#include <urcu/wfcqueue.h>
#include <urcu/wfqueue.h>
#include <urcu/wfstack.h>

#include "tap.h"

struct my_tls_struct {
	int int1;
	char char1;
	void *void1;
};

static DEFINE_URCU_TLS(int, my_tls_int);
static DEFINE_URCU_TLS(struct my_tls_struct, my_tls_struct);

static void test_lfstack(void)
{
	struct cds_lfs_stack s;

	cds_lfs_init(&s);
	ok(cds_lfs_empty(&s), "cds_lfs_empty");
}

static void test_wfstack(void)
{
	struct cds_wfs_stack s;

	cds_wfs_init(&s);
	ok(cds_wfs_empty(&s), "cds_lfs_empty");
}

static void test_wfcqueue(void)
{
	struct cds_wfcq_head head;
	struct cds_wfcq_tail tail;

	cds_wfcq_init(&head, &tail);
	ok(cds_wfcq_empty(&head, &tail), "cds_wfcq_empty");
}

static
void test_build_cds_list_head_init(void)
{
	/* Test that the CDS_LIST_HEAD_INIT macro builds correctly.  */
	struct struct_with_list {
		struct cds_list_head head;
	};

	struct struct_with_list list = {
		.head = CDS_LIST_HEAD_INIT(list.head),
	};
}

static
void test_urcu_tls(void)
{
	URCU_TLS(my_tls_int) = 1;
	URCU_TLS(my_tls_struct).int1 = 1;
	URCU_TLS(my_tls_struct).char1 = 'a';
	URCU_TLS(my_tls_struct).void1 = NULL;
}

struct an_opaque_struct;
struct a_clear_struct
{
	int x;
};

static
void test_build_rcu_dereference(void)
{
	static struct an_opaque_struct *opaque = NULL;
	static struct an_opaque_struct *const opaque_const = NULL;
	static struct a_clear_struct *clear = NULL;
	static struct a_clear_struct *const clear_const = NULL;

	rcu_dereference(opaque);
	rcu_dereference(opaque_const);
	rcu_dereference(clear);
	rcu_dereference(clear_const);
}

int main(void)
{
	plan_tests(3);

	test_lfstack();
	test_wfstack();
	test_wfcqueue();
	test_build_cds_list_head_init();
	test_urcu_tls();
	test_build_rcu_dereference();

	return exit_status();
}
