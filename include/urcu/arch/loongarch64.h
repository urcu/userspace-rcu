#ifndef _URCU_ARCH_LOONGARCH64_H
#define _URCU_ARCH_LOONGARCH64_H

/*
 * arch_loongarch.h: trivial definitions for the LOONGARCH architecture.
 */

#include <urcu/compiler.h>
#include <urcu/config.h>
#include <urcu/syscall-compat.h>

#ifdef __cplusplus
extern "C" {
#endif

#define CAA_CACHE_LINE_SIZE	128

#define cmm_mb()			__asm__ __volatile__ (		    \
					"	DBAR 0			\n" \
					:::"memory")

#ifdef __cplusplus
}
#endif

#include <urcu/arch/generic.h>

#endif /* _URCU_ARCH_LOONGARCH64_H */
