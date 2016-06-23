#ifndef _COMPAT_RAND_H
#define _COMPAT_RAND_H

/*
 * compat-rand.h
 *
 * Userspace RCU library - rand/rand_r Compatibility Header
 *
 * Copyright 1996 - Ulrich Drepper <drepper@cygnus.com >
 * Copyright 2013 - Pierre-Luc St-Charles <pierre-luc.st-charles@polymtl.ca>
 *
 * Note: this file is only used to simplify the code required to
 * use the 'rand_r(...)' system function across multiple platforms,
 * which might not always be referenced the same way.
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

#ifndef HAVE_RAND_R
/*
 * Reentrant random function from POSIX.1c.
 * Copyright (C) 1996, 1999 Free Software Foundation, Inc.
 * This file is part of the GNU C Library.
 * Contributed by Ulrich Drepper <drepper@cygnus.com <mailto:drepper@cygnus.com>>, 1996.
 */
static inline int rand_r(unsigned int *seed)
{
       unsigned int next = *seed;
       int result;

       next *= 1103515245;
       next += 12345;
       result = (unsigned int) (next / 65536) % 2048;

       next *= 1103515245;
       next += 12345;
       result <<= 10;
       result ^= (unsigned int) (next / 65536) % 1024;

       next *= 1103515245;
       next += 12345;
       result <<= 10;
       result ^= (unsigned int) (next / 65536) % 1024;

       *seed = next;

       return result;
}
#endif /* HAVE_RAND_R */

#endif /* _COMPAT_RAND_H */
