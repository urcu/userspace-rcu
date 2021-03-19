dnl SPDX-License-Identifier: LGPL-2.1-only
dnl
dnl Copyright (C) 2021 EfficiOS, Inc.
dnl
dnl Process this file with autoconf to produce a configure script.

# Project version information
m4_define([urcu_version_major], [0])
m4_define([urcu_version_minor], [12])
m4_define([urcu_version_patch], [0])
m4_define([urcu_version_dev_stage], [])
m4_define([urcu_version], urcu_version_major[.]urcu_version_minor[.]urcu_version_patch[]urcu_version_dev_stage)

# Library version information of "liburcu"
# Following the numbering scheme proposed by libtool for the library version
# http://www.gnu.org/software/libtool/manual/html_node/Updating-version-info.html
m4_define([urcu_lib_version_current], [7])
m4_define([urcu_lib_version_revision], [0])
m4_define([urcu_lib_version_age], [1])
m4_define([urcu_lib_version], urcu_lib_version_current[:]urcu_lib_version_revision[:]urcu_lib_version_age)


##                     ##
## Autoconf base setup ##
##                     ##

AC_PREREQ([2.69])
AC_INIT([userspace-rcu],[urcu_version],[mathieu dot desnoyers at efficios dot com],[],[http://liburcu.org/])

AC_CONFIG_HEADERS([include/config.h include/urcu/config.h])
AC_CONFIG_AUX_DIR([config])
AC_CONFIG_MACRO_DIR([m4])

AC_CANONICAL_TARGET
AC_CANONICAL_HOST


##                     ##
## Automake base setup ##
##                     ##

AM_INIT_AUTOMAKE([1.12 foreign dist-bzip2 no-dist-gzip nostdinc -Wall -Wno-portability -Werror])
AM_MAINTAINER_MODE([enable])

# Enable silent rules by default
AM_SILENT_RULES([yes])


##                               ##
## OS and Arch specific defaults ##
##                               ##

AS_CASE([$host],
  [*-cygwin*], [LT_NO_UNDEFINED="-no-undefined"]
)


##                   ##
## C compiler checks ##
##                   ##

# Choose the C compiler
AC_PROG_CC
# AC_PROG_CC_STDC was merged in AC_PROG_CC in autoconf 2.70
m4_version_prereq([2.70], [], [AC_PROG_CC_STDC])

# Make sure the C compiler supports C99
AS_IF([test "$ac_cv_prog_cc_c99" = "no"], [AC_MSG_ERROR([The compiler does not support C99])])

# Enable available system extensions and LFS support
AC_USE_SYSTEM_EXTENSIONS
AC_SYS_LARGEFILE

# Make sure the C compiler supports __attribute__
AX_C___ATTRIBUTE__
AS_IF([test "x$ax_cv___attribute__" != "xyes"],
  [AC_MSG_ERROR([The compiler does not support __attribute__ extensions])])

# Make sure we have pthread support
AX_PTHREAD([], [AC_MSG_ERROR([Could not configure pthread support])])

# Make sure the C compiler supports weak symbols
AX_SYS_WEAK_ALIAS
AS_IF([test "x$ax_cv_sys_weak_alias" = "xno"],
  [AC_MSG_ERROR([Your platform doesn't support weak symbols.])])

# Checks for typedefs, structures, and compiler characteristics.
AC_C_INLINE
AC_C_TYPEOF
AC_TYPE_INT32_T
AC_TYPE_PID_T
AC_TYPE_SIZE_T
AC_TYPE_SSIZE_T
AC_TYPE_UINT16_T
AC_TYPE_UINT32_T
AC_TYPE_UINT64_T
AC_TYPE_UINT8_T


##               ##
## Header checks ##
##               ##

AC_HEADER_STDBOOL
AC_CHECK_HEADERS([ \
	limits.h \
	stddef.h \
	sys/param.h \
	sys/time.h \
])


##                 ##
## Programs checks ##
##                 ##

AC_PROG_AWK
AC_PROG_GREP
AC_PROG_MAKE_SET
AC_CHECK_PROGS(NPROC, [nproc gnproc])
AC_CHECK_PROG(GETCONF, [getconf])
AS_IF([test "x$NPROC" != "x"],
	[NPROC_CMD=$NPROC],
	[AS_IF([test "x$GETCONF" != "x"],
		[NPROC_CMD="$GETCONF _NPROCESSORS_ONLN"],
		[NPROC_CMD="echo 1"]
	)]
)
AC_SUBST([NPROC_CMD], [$NPROC_CMD])

# Initialize and configure libtool
LT_INIT


##                ##
## Library checks ##
##                ##

# Checks for library functions.
AC_FUNC_MMAP
AC_FUNC_FORK
AC_CHECK_FUNCS([ \
	atexit \
	getcpuid \
	gettid \
	gettimeofday \
	memeset \
	memset \
	munmap \
	rand_r \
	sched_getcpu \
	strerror \
	strtoul \
	sysconf \
])

# AC_FUNC_MALLOC causes problems when cross-compiling.
#AC_FUNC_MALLOC

# Search for clock_gettime() in -lrt
AC_SEARCH_LIBS([clock_gettime], [rt], [
  AC_DEFINE([CONFIG_RCU_HAVE_CLOCK_GETTIME], [1], [clock_gettime() is detected.])
])


##                              ##
## Optionnal features selection ##
##                              ##

# Allow to fallback to FIXME if the membarrier syscall is unavailable on the
# running kernel, when disabled, abort if the syscall is unavailable. Applies
# to default and bulletproof flavors.
# Enabled by default
AE_FEATURE_DEFAULT_ENABLE
AE_FEATURE([sys-membarrier-fallback], [Abort if sys-membarrier is needed but not available rather than using a fallback.])

# Use compiler Thread Local Storage, when disabled use pthread_getspecific() to emulate TLS.
# Enabled by default
AE_FEATURE_DEFAULT_ENABLE
AE_FEATURE([compiler-tls], [Use pthread_getspecific() to emulate Thread Local Storage (TLS) variables.])

# smp-support configure option
# Enabled by default
AE_FEATURE_DEFAULT_ENABLE
AE_FEATURE([smp-support], [Disable SMP support. Warning: only use this on uniprocessor systems.])

# RCU debugging option
# Disabled by default
AE_FEATURE_DEFAULT_DISABLE
AE_FEATURE([rcu-debug], [Enable internal debugging self-checks. Introduces a performance penalty.])

# rculfhash iterator debugging
# Disabled by default
AE_FEATURE_DEFAULT_DISABLE
AE_FEATURE([cds-lfht-iter-debug], [Enable extra debugging checks for lock-free hash table iterator traversal. Alters the rculfhash ABI. Make sure to compile both library and application with matching configuration.])


##                                                                    ##
## Set defines for optional features conditionnals in the source code ##
##                                                                    ##

AE_IF_FEATURE_DISABLED([sys-membarrier-fallback], [
  AC_DEFINE([CONFIG_RCU_FORCE_SYS_MEMBARRIER], [1], [Require the operating system to support the membarrier system call for default and bulletproof flavors.])
])

AE_IF_FEATURE_ENABLED([compiler-tls], [
  AC_DEFINE([CONFIG_RCU_TLS], [1], [Use compiler provided Thread Local Storage.])
])

AE_IF_FEATURE_ENABLED([smp-support], [
  AC_DEFINE([CONFIG_RCU_SMP], [1], [Enable SMP support. With SMP support enabled, uniprocessors are also supported. With SMP support disabled, UP systems work fine, but the behavior of SMP systems is undefined.])
])

AE_IF_FEATURE_ENABLED([rcu-debug], [
  AC_DEFINE([CONFIG_RCU_DEBUG], [1], [Enable internal debugging self-checks. Introduces a performance penalty.])
])

AE_IF_FEATURE_ENABLED([cds-lfht-iter-debug], [
  AC_DEFINE([CONFIG_CDS_LFHT_ITER_DEBUG], [1], [Enable extra debugging checks for lock-free hash table iterator traversal. Alters the rculfhash ABI. Make sure to compile both library and application with matching configuration.])
])


# From the sched_setaffinity(2)'s man page:
# ~~~~
# The CPU affinity system calls were introduced in Linux kernel 2.5.8.
# The library interfaces were introduced in glibc 2.3.  Initially, the
# glibc interfaces included a cpusetsize argument.  In glibc 2.3.3,
# the cpuset size argument was removed, but this argument was
# restored in glibc 2.3.4.
# ~~~~

# In addition to that, some vendors ported the system call to 2.4
# kernels.

# Furthermore, when the function first appeared, the MASK argument was
# an unsigned long pointer, while later it was made into a cpu_set_t
# pointer.  Systems that have the cpu_set_t version also should have
# the CPU_ZERO, CPU_SET, etc. macros.

# All this mess means we have to cater for at least 3 different
# sched_setaffinity prototypes:

# ~~~~
#  int sched_setaffinity (pid_t pid, unsigned int len, unsigned long *mask);
#  int sched_setaffinity (pid_t __pid, size_t __cpusetsize, const cpu_set_t *__cpuset);
#  int sched_setaffinity (pid_t __pid, const cpu_set_t *__mask);
# ~~~~

AC_CHECK_TYPES([cpu_set_t],
	[have_cpu_set_t="yes"],
	[have_cpu_set_t="no"],
	[#include <sched.h>])

# Confirm that we have CPU_ZERO, and it actually works.
AC_MSG_CHECKING([whether CPU_ZERO works])
AH_TEMPLATE([HAVE_CPU_ZERO], [Defined to 1 if we have CPU_ZERO and it works])
AC_COMPILE_IFELSE([AC_LANG_SOURCE([[
		#include <sched.h>
		int main()
		{
			cpu_set_t foo; CPU_ZERO(&foo);
			return 0;
		}
	]])
],[
	AC_DEFINE(HAVE_CPU_ZERO, 1)
	AC_MSG_RESULT([yes])
],[
	AC_MSG_RESULT([no])
])

# Confirm that we have CPU_SET, and it actually works.
AC_MSG_CHECKING([whether CPU_SET works])
AH_TEMPLATE([HAVE_CPU_SET], [Defined to 1 if we have CPU_SET and it works])
AC_COMPILE_IFELSE([AC_LANG_SOURCE([[
		#include <sched.h>
		int main()
		{
			cpu_set_t foo; CPU_SET(0, &foo);
			return 0;
		}
	]])
],[
	AC_DEFINE(HAVE_CPU_SET, 1)
	AC_MSG_RESULT([yes])
],[
	AC_MSG_RESULT([no])
])

# First check if the function is available at all.
AC_CHECK_FUNCS([sched_setaffinity],[
	# Okay, we have it.  Check if also have cpu_set_t.  If we don't,
	# then we have the first version using unsigned long, and no
	# CPU_ZERO, etc. macros.  If we do have cpu_set_t, we may have the
	# version with 2 or 3 arguments.  In that case, CPU_ZERO, etc.,
	# should also be present, but we confirm nonetheless.

	AS_IF([test "x$have_cpu_set_t" = "xyes"], [
		# We do have it.
		# Check how many arguments does sched_setaffinity take.
		# Should be 3 or 2.
		AC_MSG_CHECKING([how many arguments sched_setaffinity takes])
		AC_COMPILE_IFELSE([AC_LANG_SOURCE([[
				#include <sched.h>
				int main()
				{
					cpu_set_t foo;
					sched_setaffinity(0, sizeof (foo), &foo);
					return 0;
				}
			]])
		],
		[sched_set_affinity_args=3],
		[sched_set_affinity_args=2])
		AC_DEFINE_UNQUOTED(SCHED_SETAFFINITY_ARGS,
			$sched_set_affinity_args,
			[Defined to sched_setaffinity's number of arguments.])
		AC_MSG_RESULT([$sched_set_affinity_args])
	],[
		# No cpu_set_t, always 3 args.
		AC_DEFINE(SCHED_SETAFFINITY_ARGS, 3)
	])
])


##                                                                          ##
## Set automake variables for optional feature conditionnals in Makefile.am ##
##                                                                          ##

# Building the examples requires the shared libraries to be enabled
AM_CONDITIONAL([ENABLE_EXAMPLES], AE_IS_FEATURE_ENABLED([shared]))


##                                             ##
## Substitute variables for use in Makefile.am ##
##                                             ##

# Library versions for libtool
AC_SUBST([URCU_LIBRARY_VERSION], [urcu_lib_version])

AC_SUBST(LT_NO_UNDEFINED)

AM_CPPFLAGS="-include config.h"
AC_SUBST(AM_CPPFLAGS)

AM_CFLAGS="-Wall -Wextra -Wno-unused-parameter $PTHREAD_CFLAGS"
AC_SUBST(AM_CFLAGS)

AC_CONFIG_FILES([
	Makefile
	doc/Makefile
	doc/examples/Makefile
	include/Makefile
	src/Makefile
	tests/Makefile
	tests/common/Makefile
	tests/unit/Makefile
	tests/benchmark/Makefile
	tests/regression/Makefile
	tests/utils/Makefile
	src/liburcu.pc
	src/liburcu-bp.pc
	src/liburcu-cds.pc
	src/liburcu-qsbr.pc
	src/liburcu-mb.pc
	src/liburcu-signal.pc
])

AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_perf_global.tap], [chmod +x tests/regression/rcutorture_urcu_bp_perf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_perf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_bp_perf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_perf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_bp_perf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_rperf_global.tap], [chmod +x tests/regression/rcutorture_urcu_bp_rperf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_rperf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_bp_rperf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_rperf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_bp_rperf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_stress_global.tap], [chmod +x tests/regression/rcutorture_urcu_bp_stress_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_stress_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_bp_stress_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_stress_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_bp_stress_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_uperf_global.tap], [chmod +x tests/regression/rcutorture_urcu_bp_uperf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_uperf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_bp_uperf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_bp_uperf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_bp_uperf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_perf_global.tap], [chmod +x tests/regression/rcutorture_urcu_mb_perf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_perf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_mb_perf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_perf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_mb_perf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_rperf_global.tap], [chmod +x tests/regression/rcutorture_urcu_mb_rperf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_rperf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_mb_rperf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_rperf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_mb_rperf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_stress_global.tap], [chmod +x tests/regression/rcutorture_urcu_mb_stress_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_stress_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_mb_stress_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_stress_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_mb_stress_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_uperf_global.tap], [chmod +x tests/regression/rcutorture_urcu_mb_uperf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_uperf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_mb_uperf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_mb_uperf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_mb_uperf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_perf_global.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_perf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_perf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_perf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_perf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_perf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_rperf_global.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_rperf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_rperf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_rperf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_rperf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_rperf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_stress_global.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_stress_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_stress_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_stress_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_stress_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_stress_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_uperf_global.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_uperf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_uperf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_uperf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_membarrier_uperf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_membarrier_uperf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_perf_global.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_perf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_perf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_perf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_perf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_perf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_rperf_global.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_rperf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_rperf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_rperf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_rperf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_rperf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_stress_global.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_stress_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_stress_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_stress_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_stress_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_stress_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_uperf_global.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_uperf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_uperf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_uperf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_qsbr_uperf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_qsbr_uperf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_perf_global.tap], [chmod +x tests/regression/rcutorture_urcu_signal_perf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_perf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_signal_perf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_perf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_signal_perf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_rperf_global.tap], [chmod +x tests/regression/rcutorture_urcu_signal_rperf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_rperf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_signal_rperf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_rperf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_signal_rperf_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_stress_global.tap], [chmod +x tests/regression/rcutorture_urcu_signal_stress_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_stress_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_signal_stress_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_stress_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_signal_stress_perthread.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_uperf_global.tap], [chmod +x tests/regression/rcutorture_urcu_signal_uperf_global.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_uperf_percpu.tap], [chmod +x tests/regression/rcutorture_urcu_signal_uperf_percpu.tap])
AC_CONFIG_FILES([tests/regression/rcutorture_urcu_signal_uperf_perthread.tap], [chmod +x tests/regression/rcutorture_urcu_signal_uperf_perthread.tap])


AC_OUTPUT

#
# Mini-report on what will be built.
#

PPRINT_INIT
PPRINT_SET_INDENT(1)
PPRINT_SET_TS(38)

AS_ECHO
AS_ECHO("${PPRINT_COLOR_BLDBLU}Userspace-RCU $PACKAGE_VERSION${PPRINT_COLOR_RST}")
AS_ECHO

PPRINT_SUBTITLE([Features])

PPRINT_PROP_STRING([Target architecture], $host_cpu)

# SMP support enabled/disabled
AE_IS_FEATURE_ENABLED([smp-support]) && value=1 || value=0
PPRINT_PROP_BOOL([SMP support], $value)

# TLS
AE_IS_FEATURE_ENABLED([compiler-tls]) && value="compiler TLS" || value="pthread_getspecific()"
PPRINT_PROP_STRING([Thread Local Storage (TLS)], [$value])

# clock_gettime() available
test "x$ac_cv_search_function_clock_gettime" != "xno" && value=1 || value=0
PPRINT_PROP_BOOL([clock_gettime()], $value)

# Require membarrier
AE_IS_FEATURE_ENABLED([sys-membarrier-fallback]) && value=0 || value=1
PPRINT_PROP_BOOL([Require membarrier], $value)

# RCU debug enabled/disabled
AE_IS_FEATURE_ENABLED([rcu-debug]) && value=1 || value=0
PPRINT_PROP_BOOL([Internal debugging], $value)

# rculfhash iterator debug enabled/disabled
AE_IS_FEATURE_ENABLED([cds-lfht-iter-debug]) && value=1 || value=0
PPRINT_PROP_BOOL([Lock-free HT iterator debugging], $value)

PPRINT_PROP_BOOL([Multi-flavor support], 1)

report_bindir="`eval eval echo $bindir`"
report_libdir="`eval eval echo $libdir`"

# Print the bindir and libdir this 'make install' will install into.
AS_ECHO
PPRINT_SUBTITLE([Install directories])
PPRINT_PROP_STRING([Binaries], [$report_bindir])
PPRINT_PROP_STRING([Libraries], [$report_libdir])

