INCLUDES = -I$(top_builddir)/urcu

AM_LDFLAGS=-lpthread
AM_CFLAGS=-Wall

SUBDIRS = . tests

include_HEADERS = urcu.h $(top_srcdir)/urcu-*.h
nobase_dist_include_HEADERS = urcu/compiler.h urcu/hlist.h urcu/list.h \
		urcu/rculist.h urcu/rcuhlist.h urcu/system.h urcu/urcu-futex.h \
		urcu/uatomic_generic.h urcu/arch/generic.h urcu/wfstack.h \
		urcu/wfqueue.h urcu/rculfstack.h urcu/rculfqueue.h \
		urcu/urcu_ref.h urcu/map/*.h urcu/static/*.h
nobase_nodist_include_HEADERS = urcu/arch.h urcu/uatomic_arch.h urcu/config.h

EXTRA_DIST = $(top_srcdir)/urcu/arch/*.h $(top_srcdir)/urcu/uatomic_arch_*.h \
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

lib_LTLIBRARIES = liburcu-cds.la liburcu.la liburcu-qsbr.la \
		liburcu-mb.la liburcu-signal.la liburcu-bp.la

liburcu_cds_la_SOURCES = wfqueue.c wfstack.c rculfqueue.c rculfstack.c \
			$(COMPAT)
liburcu_cds_la_LDFLAGS = -version-info $(URCU_LIBRARY_VERSION)

liburcu_la_SOURCES = urcu.c urcu-pointer.c $(COMPAT)
liburcu_la_LIBADD = -lurcu-cds
liburcu_la_DEPENDENCIES = liburcu-cds.la
liburcu_la_LDFLAGS = -version-info $(URCU_LIBRARY_VERSION)

liburcu_qsbr_la_SOURCES = urcu-qsbr.c urcu-pointer.c $(COMPAT)
liburcu_qsbr_la_LIBADD = -lurcu-cds
liburcu_qsbr_la_DEPENDENCIES = liburcu-cds.la
liburcu_qsbr_la_LDFLAGS = -version-info $(URCU_LIBRARY_VERSION)

liburcu_mb_la_SOURCES = urcu.c urcu-pointer.c $(COMPAT)
liburcu_mb_la_CFLAGS = -DRCU_MB
liburcu_mb_la_LIBADD = -lurcu-cds
liburcu_mb_la_DEPENDENCIES = liburcu-cds.la
liburcu_mb_la_LDFLAGS = -version-info $(URCU_LIBRARY_VERSION)

liburcu_signal_la_SOURCES = urcu.c urcu-pointer.c $(COMPAT)
liburcu_signal_la_CFLAGS = -DRCU_SIGNAL
liburcu_signal_la_LIBADD = -lurcu-cds
liburcu_signal_la_DEPENDENCIES = liburcu-cds.la
liburcu_signal_la_LDFLAGS = -version-info $(URCU_LIBRARY_VERSION)

liburcu_bp_la_SOURCES = urcu-bp.c urcu-pointer.c $(COMPAT)
liburcu_bp_la_LIBADD = -lurcu-cds
liburcu_bp_la_DEPENDENCIES = liburcu-cds.la
liburcu_bp_la_LDFLAGS = -version-info $(URCU_LIBRARY_VERSION)

pkgconfigdir = $(libdir)/pkgconfig
pkgconfig_DATA = liburcu.pc liburcu-bp.pc liburcu-qsbr.pc \
	liburcu-signal.pc liburcu-mb.pc 
