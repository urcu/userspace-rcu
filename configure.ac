#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.


#AC_PREREQ([2.63])
AC_INIT([userspace-rcu], [0.2.2], [mathieu dot desnoyers at polymtl dot ca])
AC_CONFIG_AUX_DIR([config])
AC_CONFIG_MACRO_DIR([m4])
AM_INIT_AUTOMAKE([foreign dist-bzip2 no-dist-gzip])
AC_CONFIG_SRCDIR([urcu.h])
AC_CONFIG_HEADERS([config.h])

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
case $host_cpu in
	x86_64) ARCHTYPE="x86";;
	i586) ARCHTYPE="x86" ;;
	i686) ARCHTYPE="x86" ;;
	powerpc) ARCHTYPE="ppc" ;;
	ppc64) ARCHTYPE="ppc" ;;
	ppc) ARCHTYPE="ppc" ;;
	s390) ARCHTYPE="s390" ;;
	s390x) ARCHTYPE="s390" ;;
	*) ARCHTYPE="unknown";;
esac

if test "$ARCHTYPE" = "unknown"; then
	AC_MSG_ERROR([Unable to detect the architecture.])
fi
AC_SUBST(ARCHTYPE)

AM_CONDITIONAL([GCC_API], [test "x$ARCHTYPE" != xx86 -a "x$ARCHTYPE" != xppc])


AC_CONFIG_FILES([
	Makefile
	tests/Makefile
])
AC_OUTPUT
