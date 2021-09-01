#ifndef _URCU_ASSERT_H
#define _URCU_ASSERT_H

/*
 * urcu/assert.h
 *
 * Userspace RCU assertion facilities.
 *
 * Copyright (c) 2021 Francis Deslauriers <francis.deslauriers@efficios.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 */

#include <urcu/config.h>

/*
 * Force usage of an expression to prevent unused expression compiler warning.
 */
#define _urcu_use_expression(_expr) ((void) sizeof((void) (_expr), 0))

#ifdef NDEBUG
/*
 * Vanilla assert() replacement. When NDEBUG is defined, the expression is
 * consumed to prevent unused variable compile warnings.
 */
# define urcu_posix_assert(_cond) _urcu_use_expression(_cond)
#else
# include <assert.h>
# define urcu_posix_assert(_cond) assert(_cond)
#endif

#if defined(DEBUG_RCU) || defined(CONFIG_RCU_DEBUG)

/*
 * Enables debugging/expensive assertions to be used in fast paths and only
 * enabled on demand. When disabled, the expression is consumed to prevent
 * unused variable compile warnings.
 */
# define urcu_assert_debug(_cond) urcu_posix_assert(_cond)
#else
# define urcu_assert_debug(_cond) _urcu_use_expression(_cond)
#endif

#endif /* _URCU_ASSERT_H */
