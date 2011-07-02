/*
 * urcu-asm.c
 *
 * Userspace RCU library - assembly dump of primitives
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

#include <urcu.h>

void show_read_lock(void)
{
	asm volatile ("/* start */");
	rcu_read_lock();
	asm volatile ("/* end */");
}

void show_read_unlock(void)
{
	asm volatile ("/* start */");
	rcu_read_unlock();
	asm volatile ("/* end */");
}
