#ifndef _URCU_CHECKER_H
#define _URCU_CHECKER_H

/*
 * urcu-checker.h
 *
 * Userspace RCU checker header
 *
 * Copyright (c) 2014 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 *
 * LGPL-compatible code should include this header with :
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

void rcu_read_lock_debug(void);
void rcu_read_unlock_debug(void);
void rcu_read_ongoing_check_debug(const char *func);

#endif /* _URCU_CHECKER_H */
