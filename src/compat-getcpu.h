#ifndef _COMPAT_GETCPU_H
#define _COMPAT_GETCPU_H

/*
 * compat-getcpu.h
 *
 * Copyright (c) 2015 Michael Jeanson <mjeanson@efficios.com>
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

#if defined(HAVE_SCHED_GETCPU)
#include <sched.h>

static inline
int urcu_sched_getcpu(void)
{
	return sched_getcpu();
}
#elif defined(HAVE_GETCPUID)
#include <sys/processor.h>

static inline
int urcu_sched_getcpu(void)
{
	return (int) getcpuid();
}
#else

static inline
int urcu_sched_getcpu(void)
{
        return -1;
}
#endif

#endif /* _COMPAT_GETCPU_H */
