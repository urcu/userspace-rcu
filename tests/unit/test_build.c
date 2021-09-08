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

static void test_lfstack(void)
{
	struct cds_lfs_stack s;

	cds_lfs_init(&s);
	if (!cds_lfs_empty(&s))
		fail("cds_lfs_empty");
	else
		ok(1, "cds_lfs_empty");
}

static void test_wfstack(void)
{
	struct cds_wfs_stack s;

	cds_wfs_init(&s);
	if (!cds_wfs_empty(&s))
		fail("cds_lfs_empty");
	else
		ok(1, "cds_lfs_empty");
}

static void test_wfcqueue(void)
{
	struct cds_wfcq_head head;
	struct cds_wfcq_tail tail;

	cds_wfcq_init(&head, &tail);
	if (!cds_wfcq_empty(&head, &tail))
		fail("cds_wfcq_empty");
	else
		ok(1, "cds_wfcq_empty");
}

int main(void)
{
	/* Need at least 1 test to make a valid TAP test plan. */
	plan_tests(3);
	ok(1, "dummy");

	test_lfstack();
	test_wfstack();
	test_wfcqueue();

	return exit_status();
}
