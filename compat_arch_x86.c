/*
 * compat_arch_x86.c
 *
 * Userspace RCU library - x86 compatibility checks
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>
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

#include <stdio.h>
#include <pthread.h>
#include <signal.h>
#include <assert.h>
#include <urcu/uatomic_arch.h>

/*
 * It does not really matter if the constructor is called before using
 * the library, as long as the caller checks if __urcu_cas_avail < 0 and calls
 * compat_arch_init() explicitely if needed.
 */
int __attribute__((constructor)) __urcu_cas_init(void);

static pthread_mutex_t compat_mutex = PTHREAD_MUTEX_INITIALIZER;

/*
 * -1: unknown
 *  1: available
 *  0: unavailable
 */
int __urcu_cas_avail = -1;

/*
 * Imported from glibc 2.3.5. linuxthreads/sysdeps/i386/pt-machine.h.
 */

int get_eflags (void)
{
	int res;
	__asm__ __volatile__ ("pushfl; popl %0" : "=r" (res) : );
	return res;
}

void set_eflags (int newflags)
{
	__asm__ __volatile__ ("pushl %0; popfl" : : "r" (newflags) : "cc");
}

int compare_and_swap_is_available (void)
{
	int oldflags = get_eflags ();
	int changed;
	/* Flip AC bit in EFLAGS.  */
	set_eflags (oldflags ^ 0x40000);
	/* See if bit changed.  */
	changed = (get_eflags () ^ oldflags) & 0x40000;
	/* Restore EFLAGS.  */
	set_eflags (oldflags);
	/* If the AC flag did not change, it's a 386 and it lacks cmpxchg.
	Otherwise, it's a 486 or above and it has cmpxchg.  */
	return changed != 0;
}

unsigned long _compat_uatomic_cmpxchg(void *addr, unsigned long old,
			      unsigned long _new, int len)
{
	sigset_t newmask, oldmask;
	int ret;

	/* Disable signals */
	ret = sigemptyset(&newmask);
	assert(!ret);
	ret = pthread_sigmask(SIG_SETMASK, &newmask, &oldmask);
	assert(!ret);
	ret = pthread_mutex_lock(&compat_mutex);
	assert(!ret);

	switch (len) {
	case 1:
	{
		unsigned char result = *(unsigned char *)addr;
		if (result == old)
			*(unsigned char *)addr = (unsigned char)_new;
		return result;
	}
	case 2:
	{
		unsigned short result = *(unsigned short *)addr;
		if (result == old)
			*(unsigned short *)addr = (unsigned short)_new;
		return result;
	}
	case 4:
	{
		unsigned int result = *(unsigned int *)addr;
		if (result == old)
			*(unsigned int *)addr = (unsigned int)_new;
		return result;
	}
	}
	/* generate an illegal instruction. Cannot catch this with linker tricks
	 * when optimizations are disabled. */
	__asm__ __volatile__("ud2");
	return 0;

	ret = pthread_mutex_unlock(&compat_mutex);
	assert(!ret);
	ret = pthread_sigmask(SIG_SETMASK, &oldmask, NULL);
	assert(!ret);
}

int __urcu_cas_init(void)
{
	if (__urcu_cas_avail < 0)
		__urcu_cas_avail = compare_and_swap_is_available();
	return __urcu_cas_avail;
}
