/*
 * urcu/map/urcu-signal.h
 *
 * Userspace RCU header -- name mapping to allow multiple flavors to be
 * used in the same executable.
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 *
 * LGPL-compatible code should include this header with :
 *
 * #define _LGPL_SOURCE
 * #include <urcu.h>
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
 *
 * IBM's contributions to this file may be relicensed under LGPLv2 or later.
 */

#define rcu_read_lock			urcu_signal_read_lock
#define _rcu_read_lock			_urcu_signal_read_lock
#define rcu_read_unlock			urcu_signal_read_unlock
#define _rcu_read_unlock		_urcu_signal_read_unlock
#define rcu_read_ongoing		urcu_signal_read_ongoing
#define _rcu_read_ongoing		_urcu_signal_read_ongoing
#define rcu_quiescent_state		urcu_signal_quiescent_state
#define _rcu_quiescent_state		_urcu_signal_quiescent_state
#define rcu_thread_offline		urcu_signal_thread_offline
#define rcu_thread_online		urcu_signal_thread_online
#define rcu_register_thread		urcu_signal_register_thread
#define rcu_unregister_thread		urcu_signal_unregister_thread
#define rcu_init			urcu_signal_init
#define rcu_exit			urcu_signal_exit
#define synchronize_rcu			urcu_signal_synchronize_rcu
#define rcu_reader			urcu_signal_reader
#define rcu_gp				urcu_signal_gp

#define get_cpu_call_rcu_data		urcu_signal_get_cpu_call_rcu_data
#define get_call_rcu_thread		urcu_signal_get_call_rcu_thread
#define create_call_rcu_data		urcu_signal_create_call_rcu_data
#define set_cpu_call_rcu_data		urcu_signal_set_cpu_call_rcu_data
#define get_default_call_rcu_data	urcu_signal_get_default_call_rcu_data
#define get_call_rcu_data		urcu_signal_get_call_rcu_data
#define get_thread_call_rcu_data	urcu_signal_get_thread_call_rcu_data
#define set_thread_call_rcu_data	urcu_signal_set_thread_call_rcu_data
#define create_all_cpu_call_rcu_data	urcu_signal_create_all_cpu_call_rcu_data
#define free_all_cpu_call_rcu_data	urcu_signal_free_all_cpu_call_rcu_data
#define call_rcu			urcu_signal_call_rcu
#define call_rcu_data_free		urcu_signal_call_rcu_data_free
#define call_rcu_before_fork		urcu_signal_call_rcu_before_fork
#define call_rcu_after_fork_parent	urcu_signal_call_rcu_after_fork_parent
#define call_rcu_after_fork_child	urcu_signal_call_rcu_after_fork_child
#define rcu_barrier			urcu_signal_barrier

#define defer_rcu			urcu_signal_defer_rcu
#define rcu_defer_register_thread	urcu_signal_defer_register_thread
#define rcu_defer_unregister_thread	urcu_signal_defer_unregister_thread
#define rcu_defer_barrier		urcu_signal_defer_barrier
#define rcu_defer_barrier_thread	urcu_signal_defer_barrier_thread
#define rcu_defer_exit			urcu_signal_defer_exit

#define rcu_flavor			urcu_signal_flavor

#define urcu_register_rculfhash_atfork		\
		urcu_signal_register_rculfhash_atfork
#define urcu_unregister_rculfhash_atfork	\
		urcu_signal_unregister_rculfhash_atfork


/* Aliases for ABI(6) compat */

#define alias_rcu_flavor		rcu_flavor_sig

/* src/urcu.c */
#define alias_rcu_read_lock		rcu_read_lock_sig
#define alias_rcu_read_unlock		rcu_read_unlock_sig
#define alias_rcu_read_ongoing		rcu_read_ongoing_sig
#define alias_rcu_register_thread	rcu_register_thread_sig
#define alias_rcu_unregister_thread	rcu_unregister_thread_sig
#define alias_rcu_init			rcu_init_sig
#define alias_rcu_exit			rcu_exit_sig
#define alias_synchronize_rcu		synchronize_rcu_sig
#define alias_rcu_reader		rcu_reader_sig
#define alias_rcu_gp			rcu_gp_sig

/* src/urcu-call-rcu-impl.h */
#define alias_get_cpu_call_rcu_data	get_cpu_call_rcu_data_sig
#define alias_get_call_rcu_thread	get_call_rcu_thread_sig
#define alias_create_call_rcu_data	create_call_rcu_data_sig
#define alias_set_cpu_call_rcu_data	set_cpu_call_rcu_data_sig
#define alias_get_default_call_rcu_data	get_default_call_rcu_data_sig
#define alias_get_call_rcu_data		get_call_rcu_data_sig
#define alias_get_thread_call_rcu_data	get_thread_call_rcu_data_sig
#define alias_set_thread_call_rcu_data	set_thread_call_rcu_data_sig
#define alias_create_all_cpu_call_rcu_data	\
		create_all_cpu_call_rcu_data_sig
#define alias_free_all_cpu_call_rcu_data	\
		free_all_cpu_call_rcu_data_sig
#define alias_call_rcu			call_rcu_sig
#define alias_call_rcu_data_free	call_rcu_data_free_sig
#define alias_call_rcu_before_fork	call_rcu_before_fork_sig
#define alias_call_rcu_after_fork_parent	\
		call_rcu_after_fork_parent_sig
#define alias_call_rcu_after_fork_child	call_rcu_after_fork_child_sig
#define alias_rcu_barrier		rcu_barrier_sig

#define alias_urcu_register_rculfhash_atfork	\
		urcu_register_rculfhash_atfork_sig
#define alias_urcu_unregister_rculfhash_atfork	\
		urcu_unregister_rculfhash_atfork_sig

/* src/urcu-defer-impl.h */
#define alias_defer_rcu			defer_rcu_sig
#define alias_rcu_defer_register_thread	rcu_defer_register_thread_sig
#define alias_rcu_defer_unregister_thread	\
		rcu_defer_unregister_thread_sig
#define alias_rcu_defer_barrier		rcu_defer_barrier_sig
#define alias_rcu_defer_barrier_thread	rcu_defer_barrier_thread_sig
#define alias_rcu_defer_exit		rcu_defer_exit_sig


/* Compat identifiers for prior undocumented multiflavor usage */
#ifndef URCU_NO_COMPAT_IDENTIFIERS

#define rcu_dereference_sig		urcu_signal_dereference
#define rcu_cmpxchg_pointer_sig		urcu_signal_cmpxchg_pointer
#define rcu_xchg_pointer_sig		urcu_signal_xchg_pointer
#define rcu_set_pointer_sig		urcu_signal_set_pointer

#define rcu_sig_before_fork		urcu_signal_before_fork
#define rcu_sig_after_fork_parent	urcu_signal_after_fork_parent
#define rcu_sig_after_fork_child	urcu_signal_after_fork_child

#define rcu_read_lock_sig		urcu_signal_read_lock
#define _rcu_read_lock_sig		_urcu_signal_read_lock
#define rcu_read_unlock_sig		urcu_signal_read_unlock
#define _rcu_read_unlock_sig		_urcu_signal_read_unlock
#define rcu_read_ongoing_sig		urcu_signal_read_ongoing
#define _rcu_read_ongoing_sig		_urcu_signal_read_ongoing
#define rcu_register_thread_sig		urcu_signal_register_thread
#define rcu_unregister_thread_sig	urcu_signal_unregister_thread
#define rcu_init_sig			urcu_signal_init
#define rcu_exit_sig			urcu_signal_exit
#define synchronize_rcu_sig		urcu_signal_synchronize_rcu
#define rcu_reader_sig			urcu_signal_reader
#define rcu_gp_sig			urcu_signal_gp

#define get_cpu_call_rcu_data_sig	urcu_signal_get_cpu_call_rcu_data
#define get_call_rcu_thread_sig		urcu_signal_get_call_rcu_thread
#define create_call_rcu_data_sig	urcu_signal_create_call_rcu_data
#define set_cpu_call_rcu_data_sig	urcu_signal_set_cpu_call_rcu_data
#define get_default_call_rcu_data_sig	urcu_signal_get_default_call_rcu_data
#define get_call_rcu_data_sig		urcu_signal_get_call_rcu_data
#define get_thread_call_rcu_data_sig	urcu_signal_get_thread_call_rcu_data
#define set_thread_call_rcu_data_sig	urcu_signal_set_thread_call_rcu_data
#define create_all_cpu_call_rcu_data_sig	\
		urcu_signal_create_all_cpu_call_rcu_data
#define free_all_cpu_call_rcu_data_sig	urcu_signal_free_all_cpu_call_rcu_data
#define call_rcu_sig			urcu_signal_call_rcu
#define call_rcu_data_free_sig		urcu_signal_call_rcu_data_free
#define call_rcu_before_fork_sig		\
		urcu_signal_call_rcu_before_fork
#define call_rcu_after_fork_parent_sig	urcu_signal_call_rcu_after_fork_parent
#define call_rcu_after_fork_child_sig	urcu_signal_call_rcu_after_fork_child
#define rcu_barrier_sig			urcu_signal_barrier

#define defer_rcu_sig			urcu_signal_defer_rcu
#define rcu_defer_register_thread_sig	urcu_signal_defer_register_thread
#define rcu_defer_unregister_thread_sig	urcu_signal_defer_unregister_thread
#define rcu_defer_barrier_sig		urcu_signal_defer_barrier
#define rcu_defer_barrier_thread_sig	urcu_signal_defer_barrier_thread
#define rcu_defer_exit_sig		urcu_signal_defer_exit

#define rcu_flavor_sig			urcu_signal_flavor

#define urcu_register_rculfhash_atfork_sig	\
		urcu_signal_register_rculfhash_atfork
#define urcu_unregister_rculfhash_atfork_sig	\
		urcu_signal_unregister_rculfhash_atfork

#endif /* URCU_NO_COMPAT_IDENTIFIERS */
