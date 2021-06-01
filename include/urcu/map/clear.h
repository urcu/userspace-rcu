/*
 * map/urcu-clear.h
 *
 * Userspace RCU header -- name mapping to allow multiple flavors to be
 * used in the same executable.
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 *
 * LGPL-compatible code should include this header with :
 *
 * #undef _LGPL_SOURCE
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

#undef rcu_read_lock
#undef _rcu_read_lock
#undef rcu_read_unlock
#undef _rcu_read_unlock
#undef rcu_read_ongoing
#undef _rcu_read_ongoing
#undef rcu_quiescent_state
#undef _rcu_quiescent_state
#undef rcu_thread_offline
#undef rcu_thread_online
#undef rcu_register_thread
#undef rcu_unregister_thread
#undef rcu_init
#undef rcu_exit
#undef synchronize_rcu
#undef rcu_reader
#undef rcu_gp

#undef get_cpu_call_rcu_data
#undef get_call_rcu_thread
#undef create_call_rcu_data
#undef set_cpu_call_rcu_data
#undef get_default_call_rcu_data
#undef get_call_rcu_data
#undef get_thread_call_rcu_data
#undef set_thread_call_rcu_data
#undef create_all_cpu_call_rcu_data
#undef free_all_cpu_call_rcu_data
#undef call_rcu
#undef call_rcu_data_free
#undef call_rcu_before_fork
#undef call_rcu_after_fork_parent
#undef call_rcu_after_fork_child
#undef rcu_barrier

#undef defer_rcu
#undef rcu_defer_register_thread
#undef rcu_defer_unregister_thread
#undef rcu_defer_barrier

#undef rcu_defer_barrier_thread
#undef rcu_defer_exit

#undef rcu_flavor

#undef urcu_register_rculfhash_atfork
#undef urcu_unregister_rculfhash_atfork
