/*
 * Atomic exchange operations for the RISC-V architecture. Let GCC do it.
 *
 * Copyright (c) 2018 Michael Jeanson <mjeanson@efficios.com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to
 * deal in the Software without restriction, including without limitation the
 * rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
 * IN THE SOFTWARE.
 */

#ifndef _URCU_ARCH_UATOMIC_RISCV_H
#define _URCU_ARCH_UATOMIC_RISCV_H

#include <urcu/compiler.h>
#include <urcu/system.h>

/*
 * See <https://gcc.gnu.org/bugzilla/show_bug.cgi?id=104831> for details.
 *
 * Until the following patches are backported, Userspace RCU is broken for the
 * RISC-V architecture when compiled with GCC.
 *
 *  - <https://gcc.gnu.org/git/?p=gcc.git;a=commit;h=4990cf84c460f064d6281d0813f20b0ef20c7448>
 *  - <https://gcc.gnu.org/git/?p=gcc.git;a=commit;h=4990cf84c460f064d6281d0813f20b0ef20c7448>
 *  - <https://gcc.gnu.org/git/?p=gcc.git;a=commit;h=d199d2e56da2379004e7e0457150409c0c99d3e6>
 */
#ifdef URCU_GCC_VERSION
# error "Implementations of some atomic operations of GCC for RISC-V are insufficient for sequential consistency. For this reason Userspace RCU is currently marked as 'broken' for RISC-V with GCC. However, it is still possible to use other toolchains."
#endif

#ifdef __cplusplus
extern "C" {
#endif

#define UATOMIC_HAS_ATOMIC_BYTE
#define UATOMIC_HAS_ATOMIC_SHORT

#ifdef __cplusplus
}
#endif

#include <urcu/uatomic/generic.h>

#endif /* _URCU_ARCH_UATOMIC_RISCV_H */
