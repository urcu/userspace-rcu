AM_CPPFLAGS += -I$(top_srcdir)/include -I$(top_builddir)/include -I$(top_srcdir)/src

#Add the -version-info directly here since we are only building
# library that use the version-info
AM_LDFLAGS=-version-info $(URCU_LIBRARY_VERSION)
if USE_CYGWIN
AM_LDFLAGS+=-no-undefined
endif

include_HEADERS = urcu.h urcu-bp.h urcu-call-rcu.h urcu-defer.h \
		urcu-pointer.h urcu-qsbr.h urcu-flavor.h

dist_noinst_HEADERS = urcu-die.h urcu-wait.h compat-getcpu.h \
	compat-rand.h


if COMPAT_ARCH
COMPAT=compat_arch_@ARCHTYPE@.c
else
COMPAT=
endif

COMPAT+=compat_futex.c

RCULFHASH = rculfhash.c rculfhash-mm-order.c rculfhash-mm-chunk.c \
		rculfhash-mm-mmap.c

lib_LTLIBRARIES = liburcu-common.la \
		liburcu.la liburcu-qsbr.la \
		liburcu-mb.la liburcu-signal.la liburcu-bp.la \
		liburcu-cds.la

#
# liburcu-common contains wait-free queues (needed by call_rcu) as well
# as futex fallbacks.
#
liburcu_common_la_SOURCES = wfqueue.c wfcqueue.c wfstack.c $(COMPAT)

liburcu_la_SOURCES = urcu.c urcu-pointer.c $(COMPAT)
liburcu_la_LIBADD = liburcu-common.la

liburcu_qsbr_la_SOURCES = urcu-qsbr.c urcu-pointer.c $(COMPAT)
liburcu_qsbr_la_LIBADD = liburcu-common.la

liburcu_mb_la_SOURCES = urcu.c urcu-pointer.c $(COMPAT)
liburcu_mb_la_CFLAGS = -DRCU_MB $(AM_CFLAGS)
liburcu_mb_la_LIBADD = liburcu-common.la

liburcu_signal_la_SOURCES = urcu.c urcu-pointer.c $(COMPAT)
liburcu_signal_la_CFLAGS = -DRCU_SIGNAL $(AM_CFLAGS)
liburcu_signal_la_LIBADD = liburcu-common.la

liburcu_bp_la_SOURCES = urcu-bp.c urcu-pointer.c $(COMPAT)
liburcu_bp_la_LIBADD = liburcu-common.la

liburcu_cds_la_SOURCES = rculfqueue.c rculfstack.c lfstack.c \
	workqueue.c workqueue.h $(RCULFHASH) $(COMPAT)
liburcu_cds_la_LIBADD = liburcu-common.la

pkgconfigdir = $(libdir)/pkgconfig
pkgconfig_DATA = liburcu-cds.pc liburcu.pc liburcu-bp.pc liburcu-qsbr.pc \
	liburcu-signal.pc liburcu-mb.pc

EXTRA_DIST = compat_arch_x86.c \
	urcu-call-rcu-impl.h \
	urcu-defer-impl.h \
	rculfhash-internal.h
