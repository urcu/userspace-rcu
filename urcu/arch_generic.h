#ifndef _URCU_ARCH_GENERIC_H
#define _URCU_ARCH_GENERIC_H

/*
 * arch_generic.h: common definitions for multiple architectures.
 *
 * Copyright (c) 2010 Paolo Bonzini <pbonzini@redhat.com>
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

#include <urcu/compiler.h>
#include <urcu/config.h>

#ifdef __cplusplus
extern "C" {
#endif

#ifndef CACHE_LINE_SIZE
#define CACHE_LINE_SIZE	64
#endif

#if !defined(mc) && !defined(rmc) && !defined(wmc)
#define CONFIG_HAVE_MEM_COHERENCY
/*
 * Architectures with cache coherency must _not_ define mc/rmc/wmc.
 *
 * For them, mc/rmc/wmc are implemented with a * simple compiler barrier;
 * in addition, we provide defaults for mb (using GCC builtins) as well as
 * rmb and wmb (defaulting to mb).
 */

#ifndef mb
#define mb()    __sync_synchronize()
#endif

#ifndef rmb
#define rmb()    mb()
#endif

#ifndef wmb
#define wmb()    mb()
#endif

#define mc()	 barrier()
#define rmc()	 barrier()
#define wmc()	 barrier()
#else
/*
 * Architectures without cache coherency need something like the following:
 *
 * #define mc()		arch_cache_flush() 
 * #define rmc()	arch_cache_flush_read()
 * #define wmc()	arch_cache_flush_write()
 *
 * Of these, only mc is mandatory.  rmc and wmc default to mc.  mb/rmb/wmb
 * use these definitions by default:
 *
 * #define mb()		mc()
 * #define rmb()	rmc()
 * #define wmb()	wmc()
 */

#ifndef mb
#define mb()    mc()
#endif

#ifndef rmb
#define rmb()    rmc()
#endif

#ifndef wmb
#define wmb()    wmc()
#endif

#ifndef rmc
#define rmc()    mc()
#endif

#ifndef wmc
#define wmc()    mc()
#endif
#endif

/* Nop everywhere except on alpha. */
#ifndef read_barrier_depends
#define read_barrier_depends()
#endif

#ifdef CONFIG_RCU_SMP
#define smp_mb()	mb()
#define smp_rmb()	rmb()
#define smp_wmb()	wmb()
#define smp_mc()	mc()
#define smp_rmc()	rmc()
#define smp_wmc()	wmc()
#define smp_read_barrier_depends()	read_barrier_depends()
#else
#define smp_mb()	barrier()
#define smp_rmb()	barrier()
#define smp_wmb()	barrier()
#define smp_mc()	barrier()
#define smp_rmc()	barrier()
#define smp_wmc()	barrier()
#define smp_read_barrier_depends()
#endif

#ifndef cpu_relax
#define cpu_relax()	 barrier()
#endif

#ifdef __cplusplus
}
#endif

#endif /* _URCU_ARCH_GENERIC_H */
