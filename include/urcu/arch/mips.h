#ifndef _URCU_ARCH_MIPS_H
#define _URCU_ARCH_MIPS_H

/*
 * arch_mips.h: trivial definitions for the MIPS architecture.
 *
 * Copyright (c) 2010 Paolo Bonzini <pbonzini@redhat.com>
 * Copyright (c) 2012 Ralf Baechle <ralf@linux-mips.org>
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
#include <urcu/syscall-compat.h>

#ifdef __cplusplus
extern "C" {
#endif

#define cmm_mb()			__asm__ __volatile__ (		    \
					"	.set	mips2		\n" \
					"	sync			\n" \
					"	.set	mips0		\n" \
					:::"memory")

#ifdef __cplusplus
}
#endif

#include <urcu/arch/generic.h>

#endif /* _URCU_ARCH_MIPS_H */
