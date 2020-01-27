#ifndef _URCU_SYSCALL_COMPAT_H
#define _URCU_SYSCALL_COMPAT_H

/*
 * urcu/syscall-compat.h
 *
 * Userspace RCU library - Syscall Compatibility Header
 *
 * Copyright 2013 - Pierre-Luc St-Charles <pierre-luc.st-charles@polymtl.ca>
 *
 * Note: this file is only used to simplify the code required to
 * include the 'syscall.h' system header across multiple platforms,
 * which might not always be located at the same place (or needed at all).
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

#if defined(__ANDROID__) || defined(__sun__) || defined(__GNU__)
#include <sys/syscall.h>
#elif defined(__linux__) || defined(__GLIBC__)
#include <syscall.h>

#elif defined(__CYGWIN__) || defined(__APPLE__) || \
	defined(__FreeBSD__) || defined(__DragonFly__)
/* Don't include anything on these platforms. */

#else
#error "Add platform support to urcu/syscall-compat.h"
#endif

#endif /* _URCU_SYSCALL_COMPAT_H */
