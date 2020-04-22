AC_PREREQ(2.59)
AC_INIT([userspace-rcu],[0.12.1],[mathieu dot desnoyers at efficios dot com], [], [http://liburcu.org/])

# Following the numbering scheme proposed by libtool for the library version
# http://www.gnu.org/software/libtool/manual/html_node/Updating-version-info.html
AC_SUBST([URCU_LIBRARY_VERSION], [7:0:1])

AC_CONFIG_HEADERS([include/config.h include/urcu/config.h])
AC_CONFIG_AUX_DIR([config])
AC_CONFIG_MACRO_DIR([m4])

AC_CANONICAL_TARGET
AC_CANONICAL_HOST

AM_INIT_AUTOMAKE([1.12 foreign dist-bzip2 no-dist-gzip nostdinc])
AM_MAINTAINER_MODE([enable])

# Enable silent rules if available (Introduced in AM 1.11)
m4_ifdef([AM_SILENT_RULES], [AM_SILENT_RULES([yes])])

AC_REQUIRE_AUX_FILE([tap-driver.sh])

AH_TEMPLATE([CONFIG_RCU_SMP], [Enable SMP support. With SMP support enabled, uniprocessors are also supported. With SMP support disabled, UP systems work fine, but the behavior of SMP systems is undefined.])
AH_TEMPLATE([CONFIG_RCU_HAVE_FENCE], [Defined when on a system that has memory fence instructions.])
AH_TEMPLATE([CONFIG_RCU_HAVE_FUTEX], [Defined when on a system with futex support.])
AH_TEMPLATE([CONFIG_RCU_COMPAT_ARCH], [Compatibility mode for i386 which lacks cmpxchg instruction.])
AH_TEMPLATE([CONFIG_RCU_ARM_HAVE_DMB], [Use the dmb instruction if available for use on ARM.])
AH_TEMPLATE([CONFIG_RCU_TLS], [TLS provided by the compiler.])
AH_TEMPLATE([CONFIG_RCU_HAVE_CLOCK_GETTIME], [clock_gettime() is detected.])
AH_TEMPLATE([CONFIG_RCU_FORCE_SYS_MEMBARRIER], [Require the operating system to support the membarrier system call for default and bulletproof flavors.])
AH_TEMPLATE([CONFIG_RCU_DEBUG], [Enable internal debugging self-checks. Introduce performance penalty.])
AH_TEMPLATE([CONFIG_CDS_LFHT_ITER_DEBUG], [Enable extra debugging checks for lock-free hash table iterator traversal. Alters the rculfhash ABI. Make sure to compile both library and application with matching configuration.])

# Allow requiring the operating system to support the membarrier system
# call. Applies to default and bulletproof flavors.
AC_ARG_ENABLE([sys-membarrier-fallback],
	AS_HELP_STRING([--disable-sys-membarrier-fallback], [Abort if sys-membarrier is needed but not available rather than using a fallback.]),
	[def_sys_membarrier_fallback=$enableval],
	[def_sys_membarrier_fallback="yes"])
AS_IF([test "x$def_sys_membarrier_fallback" != "xyes"], [AC_DEFINE([CONFIG_RCU_FORCE_SYS_MEMBARRIER], [1])])

# Allow overriding storage used for TLS variables.
AC_ARG_ENABLE([compiler-tls],
	AS_HELP_STRING([--disable-compiler-tls], [Use pthread_getspecific() to emulate Thread Local Storage (TLS) variables.]),
	[def_compiler_tls=$enableval],
	[def_compiler_tls="yes"])

# Checks for C compiler
AC_USE_SYSTEM_EXTENSIONS
AC_PROG_CC
AC_PROG_CC_STDC

AS_IF([test "x$def_compiler_tls" = "xyes"], AC_DEFINE([CONFIG_RCU_TLS], [1]), [:])

# Checks for programs.
AC_PROG_AWK
AC_PROG_MAKE_SET
AC_CHECK_PROGS(NPROC, [nproc gnproc])
AC_CHECK_PROGS(GETCONF, [getconf])
AS_IF([test "x$NPROC" != "x"],
	[NPROC_CMD=$NPROC],
	[AS_IF([test "x$GETCONF" != "x"],
		[NPROC_CMD="$GETCONF _NPROCESSORS_ONLN"],
		[NPROC_CMD="echo 1"]
	)]
)
AC_SUBST([NPROC_CMD], [$NPROC_CMD])

LT_INIT

# Checks for typedefs, structures, and compiler characteristics.
AC_C_INLINE
AC_TYPE_PID_T
AC_TYPE_SIZE_T
AC_TYPE_SSIZE_T
AC_TYPE_UINT16_T
AC_TYPE_INT32_T
AC_TYPE_UINT32_T
AC_TYPE_UINT64_T
AC_TYPE_UINT8_T

AX_C___ATTRIBUTE__
AS_IF([test "x$ax_cv___attribute__" = "xyes"],
	[:],
	[AC_MSG_ERROR([The compiler does not support __attribute__ extensions])])

AX_PTHREAD(,[AC_MSG_ERROR([Could not configure pthreads support])])

AM_CFLAGS="$AM_CFLAGS $PTHREAD_CFLAGS"

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

# Check for headers
AC_HEADER_STDBOOL
AC_CHECK_HEADERS([ \
	limits.h \
	stddef.h \
	sys/param.h \
	sys/time.h \
])

# Find arch type
AS_CASE([$host_cpu],
	[k1om], [ARCHTYPE="x86"],
	[i386], [ARCHTYPE="x86" && SUBARCHTYPE="x86compat"],
	[i486], [ARCHTYPE="x86"],
	[i586], [ARCHTYPE="x86"],
	[i686], [ARCHTYPE="x86"],
	[amd64], [ARCHTYPE="x86"],
	[x86_64], [ARCHTYPE="x86"],
	[powerpc], [ARCHTYPE="ppc"],
	[ppc64], [ARCHTYPE="ppc"],
	[powerpc64], [ARCHTYPE="ppc"],
	[powerpc64le], [ARCHTYPE="ppc"],
	[ppc], [ARCHTYPE="ppc"],
	[s390], [ARCHTYPE="s390"],
	[s390x], [ARCHTYPE="s390"],
	[sparc], [ARCHTYPE="sparc64"],
	[sparc64], [ARCHTYPE="sparc64"],
	[alpha*], [ARCHTYPE="alpha"],
	[ia64], [ARCHTYPE="ia64"],
	[arm*], [ARCHTYPE="arm"],
	[aarch64*], [ARCHTYPE="aarch64"],
	[mips*], [ARCHTYPE="mips"],
	[nios2*], [ARCHTYPE="nios2"],
	[tile*], [ARCHTYPE="tile"],
	[hppa*], [ARCHTYPE="hppa"],
	[m68k], [ARCHTYPE="m68k"],
	[riscv*], [ARCHTYPE="riscv"],
	[ARCHTYPE="unknown"]
)

AS_CASE([$host],[*-cygwin*],
	[AM_CONDITIONAL(USE_CYGWIN, true)],
	[AM_CONDITIONAL(USE_CYGWIN, false)]
)

AC_SUBST(ARCHTYPE)
AC_SUBST(SUBARCHTYPE)

UATOMICSRC=include/urcu/uatomic/$ARCHTYPE.h
ARCHSRC=include/urcu/arch/$ARCHTYPE.h

AS_IF([test "x$SUBARCHTYPE" = xx86compat],[
	AC_DEFINE([CONFIG_RCU_COMPAT_ARCH], [1])
])

AS_IF([test "$host_cpu" = "armv7l"],[
	AM_CFLAGS="$AM_CFLAGS -mcpu=cortex-a9 -mtune=cortex-a9 -O1"
])

# ARM-specific checks
AS_IF([test "x$ARCHTYPE" = "xarm"],[
	AC_MSG_CHECKING([for dmb instruction])
	AC_COMPILE_IFELSE([AC_LANG_SOURCE([[
				int main()
				{
					asm volatile("dmb":::"memory");
					return 0;
				}
		]])
	],[
		AC_MSG_RESULT([yes])
		AC_DEFINE([CONFIG_RCU_ARM_HAVE_DMB], [1])
	],[
		AC_MSG_RESULT([no])
	])
])

# Tile-specific checks
AS_IF([echo "$host_cpu" | grep "^tile"],[
	AC_MSG_CHECKING([for Tile architecture type])
	AC_COMPILE_IFELSE([AC_LANG_PROGRAM([[
				#ifndef __tilegx__
				#error
				#endif
		]])
	],[
		AC_MSG_RESULT([ok])
	],[
		AC_MSG_FAILURE([URCU has only been tested on the TileGx architecture. For other Tile* architectures, please run the tests first and report the results to the maintainer so that proper support can be added.])
	])
])

# x86-specific checks
AS_IF([test "x$ARCHTYPE" = "xx86"],[
	AC_MSG_CHECKING([if architecture really supports the mfence instruction])
	#For now, using lock; addl compatibility mode even for i686, because the
	#Pentium III is seen as a i686, but lacks mfence instruction.
	#Only using fence for x86_64.
	#
	#k1om is the name for the Intel MIC family (Xeon Phi). It is an x86_64
	#variant but lacks fence instructions.
	AS_IF([test "x$host_cpu" != "xi386" -a "x$host_cpu" != "xi486" -a "x$host_cpu" != "xi586" -a "x$host_cpu" != "xi686" -a "x$host_vendor" != "xk1om" -a "x$host_cpu" != "xk1om"],[
		AC_MSG_RESULT([yes])
		AC_DEFINE([CONFIG_RCU_HAVE_FENCE], [1])
		config_rcu_have_fence=yes
	],[
		AC_MSG_RESULT([no])
		config_rcu_have_fence=no
	])
])

# Check if sys_futex() is available
AC_MSG_CHECKING([for sys_futex()])
AC_COMPILE_IFELSE([AC_LANG_SOURCE([[
		#include <sys/syscall.h>
		#ifndef __NR_futex
		#error "futexes not available"
		#endif
	]])
],[
	AC_MSG_RESULT([yes])
	AC_DEFINE([CONFIG_RCU_HAVE_FUTEX], [1])
	compat_futex_test=0
],[
	AC_MSG_RESULT([no])
	compat_futex_test=1
])

# Search for clock_gettime
AC_SEARCH_LIBS([clock_gettime], [rt], [
	AC_DEFINE([CONFIG_RCU_HAVE_CLOCK_GETTIME], [1])
	config_rcu_have_clock_gettime=yes
], [])

AM_CONDITIONAL([COMPAT_FUTEX], [test "x$compat_futex_test" = "x1"])
AM_CONDITIONAL([COMPAT_ARCH], [test "x$SUBARCHTYPE" = "xx86compat"])
AM_CONDITIONAL([NO_SHARED], [test "x$enable_shared" = "xno"])

# smp-support configure option
AC_ARG_ENABLE([smp-support], 
	AS_HELP_STRING([--disable-smp-support], [Disable SMP support. Warning: only use this on uniprocessor systems. [default=enabled]]),
	[def_smp_support=$enableval],
	[def_smp_support="yes"])
AS_IF([test "x$def_smp_support" = "xyes"], [AC_DEFINE([CONFIG_RCU_SMP], [1])])

# RCU debugging option
AC_ARG_ENABLE([rcu-debug],
      AS_HELP_STRING([--enable-rcu-debug], [Enable internal debugging
		      self-checks. Introduce performance penalty.]))
AS_IF([test "x$enable_rcu_debug" = "xyes"], [
       AC_DEFINE([CONFIG_RCU_DEBUG], [1])
])

# rculfhash iterator debugging
AC_ARG_ENABLE([cds-lfht-iter-debug],
      AS_HELP_STRING([--enable-cds-lfht-iter-debug], [Enable extra debugging checks for lock-free hash table iterator traversal. Alters the rculfhash ABI. Make sure to compile both library and application with matching configuration.]))
AS_IF([test "x$enable_cds_lfht_iter_debug" = "xyes"], [
       AC_DEFINE([CONFIG_CDS_LFHT_ITER_DEBUG], [1])
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

AM_CPPFLAGS="-include config.h"
AC_SUBST(AM_CPPFLAGS)

AM_CFLAGS="-Wall -Wextra -Wno-unused-parameter $AM_CFLAGS"
AC_SUBST(AM_CFLAGS)

AC_CONFIG_LINKS([
	include/urcu/arch.h:$ARCHSRC
	include/urcu/uatomic.h:$UATOMICSRC
])
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
test "x$def_smp_support" = "xyes" && value=1 || value=0
PPRINT_PROP_BOOL([SMP support], $value)

# Memory fence support available
test "x$config_rcu_have_fence" = "xyes" && value=1 || value=0
PPRINT_PROP_BOOL([Memory fence instructions], $value)

# Futex support available
test "x$compat_futex_test" = "x0" && value=1 || value=0
PPRINT_PROP_BOOL([Futex support], $value)

# TLS
test "x$def_compiler_tls" = "xyes" && value="compiler TLS" || value="pthread_getspecific()"
PPRINT_PROP_STRING([Thread Local Storage (TLS)], [$value])

# clock_gettime() available
test "x$config_rcu_have_clock_gettime" = "xyes" && value=1 || value=0
PPRINT_PROP_BOOL([clock_gettime()], $value)

# Require membarrier
test "x$def_sys_membarrier_fallback" != "xyes" && value=1 || value=0
PPRINT_PROP_BOOL([Require membarrier], $value)

# RCU debug enabled/disabled
test "x$enable_rcu_debug" = "xyes" && value=1 || value=0
PPRINT_PROP_BOOL([Internal debugging], $value)

# rculfhash iterator debug enabled/disabled
test "x$enable_cds_lfht_iter_debug" = "xyes" && value=1 || value=0
PPRINT_PROP_BOOL([Lock-free hash table iterator debugging], $value)

PPRINT_PROP_BOOL([Multi-flavor support], 1)

report_bindir="`eval eval echo $bindir`"
report_libdir="`eval eval echo $libdir`"

# Print the bindir and libdir this `make install' will install into.
AS_ECHO
PPRINT_SUBTITLE([Install directories])
PPRINT_PROP_STRING([Binaries], [$report_bindir])
PPRINT_PROP_STRING([Libraries], [$report_libdir])

