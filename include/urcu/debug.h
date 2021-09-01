#ifndef _URCU_DEBUG_H
#define _URCU_DEBUG_H

/*
 * urcu/debug.h
 *
 * Userspace RCU debugging facilities.
 *
 * Copyright (c) 2015 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
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

#include <assert.h>

#include <urcu/config.h>

#if defined(DEBUG_RCU) || defined(CONFIG_RCU_DEBUG)
# define urcu_assert_debug(...) assert(__VA_ARGS__)
#else
# define urcu_assert_debug(...)
#endif

/*
 * For backward compatibility reasons, this file must expose the urcu_assert()
 * macro.
 */
#define urcu_assert(_cond) urcu_assert_debug(_cond)

#endif /* _URCU_DEBUG_H */
