/*
 * test_urcu_multiflavor.c
 *
 * Userspace RCU library - test multiple RCU flavors into one program
 *
 * Copyright February 2012 - Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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

#ifndef DYNAMIC_LINK_TEST
#define _LGPL_SOURCE
#endif

#include <urcu/urcu-mb.h>
#include <urcu/urcu-bp.h>
#include <urcu/urcu-memb.h>
#include <urcu/urcu-signal.h>
#include <urcu/urcu-qsbr.h>

#include <stdlib.h>
#include "tap.h"

static int test_mf_mb(void)
{
	urcu_mb_register_thread();
	urcu_mb_read_lock();
	urcu_mb_read_unlock();
	urcu_mb_synchronize_rcu();
	urcu_mb_unregister_thread();
	return 0;
}

static int test_mf_bp(void)
{
	urcu_bp_register_thread();
	urcu_bp_read_lock();
	urcu_bp_read_unlock();
	urcu_bp_synchronize_rcu();
	urcu_bp_unregister_thread();
	return 0;
}

static int test_mf_memb(void)
{
	urcu_memb_register_thread();
	urcu_memb_read_lock();
	urcu_memb_read_unlock();
	urcu_memb_synchronize_rcu();
	urcu_memb_unregister_thread();
	return 0;
}

static int test_mf_signal(void)
{
	urcu_signal_register_thread();
	urcu_signal_read_lock();
	urcu_signal_read_unlock();
	urcu_signal_synchronize_rcu();
	urcu_signal_unregister_thread();
	return 0;
}

static int test_mf_qsbr(void)
{
	urcu_qsbr_register_thread();
	urcu_qsbr_read_lock();
	urcu_qsbr_read_unlock();
	urcu_qsbr_synchronize_rcu();
	urcu_qsbr_unregister_thread();
	return 0;
}

int main(int argc, char **argv)
{
	plan_tests(5);

	ok1(!test_mf_mb());
	ok1(!test_mf_bp());
	ok1(!test_mf_memb());
	ok1(!test_mf_signal());
	ok1(!test_mf_qsbr());

	return exit_status();
}
