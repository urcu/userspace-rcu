INCLUDES = -I$(top_builddir)/urcu

AM_LDFLAGS=-lpthread

SUBDIRS = . tests

include_HEADERS = urcu.h $(top_srcdir)/urcu-*.h
nobase_dist_include_HEADERS = urcu/compiler.h urcu/hlist.h urcu/list.h \
		urcu/rculist.h urcu/rcuhlist.h urcu/system.h urcu/urcu-futex.h \
		urcu/uatomic_generic.h urcu/arch_generic.h
nobase_nodist_include_HEADERS = urcu/arch.h urcu/uatomic_arch.h urcu/config.h

EXTRA_DIST = $(top_srcdir)/urcu/arch_*.h $(top_srcdir)/urcu/uatomic_arch_*.h \
		gpl-2.0.txt lgpl-2.1.txt lgpl-relicensing.txt \
		README LICENSE compat_arch_x86.c

if COMPAT_ARCH
COMPAT=compat_arch_@ARCHTYPE@.c
else
COMPAT=
endif

if COMPAT_FUTEX
COMPAT+=compat_futex.c
endif

lib_LTLIBRARIES = liburcu.la liburcu-qsbr.la liburcu-mb.la liburcu-signal.la liburcu-bp.la liburcu-defer.la

liburcu_la_SOURCES = urcu.c urcu-pointer.c $(COMPAT)

liburcu_qsbr_la_SOURCES = urcu-qsbr.c urcu-pointer.c $(COMPAT)

liburcu_mb_la_SOURCES = urcu.c urcu-pointer.c $(COMPAT)
liburcu_mb_la_CFLAGS = -DRCU_MB

liburcu_signal_la_SOURCES = urcu.c urcu-pointer.c $(COMPAT)
liburcu_signal_la_CFLAGS = -DRCU_SIGNAL

liburcu_bp_la_SOURCES = urcu-bp.c urcu-pointer.c $(COMPAT)

liburcu_defer_la_SOURCES = urcu-defer.c $(COMPAT)
