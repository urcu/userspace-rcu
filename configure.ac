#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.


AC_INIT([userspace-rcu], [0.3.0], [mathieu dot desnoyers at polymtl dot ca])
AC_CONFIG_AUX_DIR([config])
AC_CANONICAL_TARGET
AC_CANONICAL_HOST
AM_INIT_AUTOMAKE([foreign dist-bzip2 no-dist-gzip])
AC_CONFIG_SRCDIR([urcu.h])
AM_PROG_MKDIR_P

AC_CONFIG_HEADERS([config.h urcu/config.h])

# Keep at the end to do not pollute installed header.
AH_TEMPLATE([CONFIG_URCU_SMP], [Enable SMP support. With SMP support enabled, uniprocessors are also supported. With SMP support disabled, UP systems work fine, but the behavior of SMP systems is undefined.])
AH_TEMPLATE([CONFIG_URCU_HAVE_FENCE], [Defined when on a system that has memory fence instructions.])
AH_TEMPLATE([CONFIG_URCU_HAVE_FUTEX], [Defined when on a system with futex support.])
AH_TEMPLATE([CONFIG_URCU_COMPAT_ARCH], [Compatibility mode for i386 which lacks
cmpxchg instruction.])

# Checks for programs.
AC_PROG_CC
AC_PROG_MAKE_SET
AC_PROG_LIBTOOL

# Checks for typedefs, structures, and compiler characteristics.
AC_C_INLINE
AC_TYPE_PID_T
AC_TYPE_SIZE_T

# Checks for library functions.
AC_FUNC_MALLOC
AC_FUNC_MMAP
AC_CHECK_FUNCS([bzero gettimeofday munmap strtoul])

# Find arch type
case $target_cpu in
	i386) ARCHTYPE="x86"; SUBARCHTYPE="x86compat" ;;
	i486) ARCHTYPE="x86";;
	i586) ARCHTYPE="x86";;
	i686) ARCHTYPE="x86";;
	x86_64) ARCHTYPE="x86";;
	powerpc) ARCHTYPE="ppc" ;;
	ppc64) ARCHTYPE="ppc" ;;
	powerpc64) ARCHTYPE="ppc" ;;
	ppc) ARCHTYPE="ppc" ;;
	s390) ARCHTYPE="s390" ;;
	s390x) ARCHTYPE="s390" ;;
	sparc64) ARCHTYPE="sparc64" ;;
	*) ARCHTYPE="unknown";;
esac

if test "$ARCHTYPE" = "unknown"; then
	AC_MSG_ERROR([Unable to detect the architecture.])
fi
AC_SUBST(ARCHTYPE)
AC_SUBST(SUBARCHTYPE)

[
#if test "x$ARCHTYPE" = "xx86" -a "x$target_cpu" != "xi386" -a "x$target_cpu" != "xi486" -a "x$target_cpu" != "xi586"; then
#For now, using lock; addl compatibility mode even for i686, because the
#Pentium III is seen as a i686, but lacks mfence instruction.
#Only using fence for x86_64.
if test "x$ARCHTYPE" = "xx86" -a "x$target_cpu" != "xi386" -a "x$target_cpu" != "xi486" -a "x$target_cpu" != "xi586" -a "x$target_cpu" != "xi686"; then
]
	AC_DEFINE([CONFIG_URCU_HAVE_FENCE], [1])
[
fi
]

AC_MSG_CHECKING([sys_futex()])
AC_TRY_COMPILE(
[
#include <sys/syscall.h>
],
[
#ifndef __NR_futex
#error "futexes not available"
#endif
],
[
	AC_MSG_RESULT([yes])
	AC_DEFINE([CONFIG_URCU_HAVE_FUTEX], [1])
	compat_futex_test=0
]
,
[
	AC_MSG_RESULT([no])
	compat_futex_test=1
]
)

AM_CONDITIONAL([COMPAT_FUTEX], [ test "x$compat_futex_test" = "x1" ])

AM_CONDITIONAL([GCC_API], [test "x$ARCHTYPE" != xx86 -a "x$ARCHTYPE" != xppc])

AM_CONDITIONAL([COMPAT_ARCH], [test "x$SUBARCHTYPE" = xx86compat ])

[
if test "x$SUBARCHTYPE" = xx86compat; then
]
	AC_DEFINE([CONFIG_URCU_COMPAT_ARCH], [1])
[
fi
]

AC_ARG_ENABLE([smp-support], [  --disable-smp-support   Disable SMP support. Warning: only use this
                          on uniprocessor systems. [[default=enabled]]], [def_smp_support=$enableval], [def_smp_support="yes"])

[
if test "$def_smp_support" = "no"; then
	echo "SMP support disabled."
else
]
	AC_DEFINE([CONFIG_URCU_SMP], [1])
[
	echo "SMP support enabled."
fi
]

AC_CONFIG_FILES([
	Makefile
	tests/Makefile
])
AC_OUTPUT
