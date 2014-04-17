#ifndef _URCU_ARCH_HPPA_H
#define _URCU_ARCH_HPPA_H

#include <urcu/compiler.h>
#include <urcu/config.h>

#ifdef __cplusplus
extern "C" {
#endif

#include <stdlib.h>
#include <sys/time.h>

typedef unsigned long cycles_t;

static inline cycles_t caa_get_cycles(void)
{
	cycles_t cycles;

	asm volatile("mfctl 16, %0" : "=r" (cycles));
	return cycles;
}

#ifdef __cplusplus
}
#endif

#include <urcu/arch/generic.h>

#endif /* _URCU_ARCH_HPPA_H */
