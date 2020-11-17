#ifndef _URCU_UTILS_H
#define _URCU_UTILS_H

/*
 * urcu-utils.h
 *
 * Userspace RCU library internal utils
 *
 * Copyright (c) 2018 Michael Jeanson <mjeanson@efficios.com>
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

#include <urcu/config.h>

#define urcu_stringify(a) _urcu_stringify(a)
#define _urcu_stringify(a) #a

#define max_t(type, x, y)				\
	({						\
		type __max1 = (x);              	\
		type __max2 = (y);              	\
		__max1 > __max2 ? __max1: __max2;	\
	})

#define min_t(type, x, y)				\
	({						\
		type __min1 = (x);              	\
		type __min2 = (y);              	\
		__min1 <= __min2 ? __min1: __min2;	\
	})

/* There is no concept of symbol aliases on MacOS */
#ifdef __APPLE__
#define URCU_ATTR_ALIAS(x)
#else
#define URCU_ATTR_ALIAS(x) __attribute__((alias(x)))
#endif

#ifdef CONFIG_RCU_TLS
#define DEFINE_URCU_TLS_ALIAS_1(type, name, alias)		\
	URCU_ATTR_ALIAS(#name)					\
	extern type alias

#else
#define DEFINE_URCU_TLS_ALIAS_1(type, name, alias)		\
	URCU_ATTR_ALIAS("*__tls_access_" #name)			\
	type *__tls_access_ ## alias()
#endif

#define DEFINE_URCU_TLS_ALIAS(type, name, alias)		\
	DEFINE_URCU_TLS_ALIAS_1(type, name, alias)

#endif /* _URCU_UTILS_H */
