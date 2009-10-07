ACLOCAL_AMFLAGS = -I m4
INCLUDES = -I$(top_builddir)/urcu

AM_LDFLAGS=-lpthread

SUBDIRS = tests

include_HEADERS = urcu.h $(top_srcdir)/urcu-*.h
nobase_dist_include_HEADERS = urcu/compiler.h urcu/hlist.h urcu/list.h urcu/rculist.h urcu/system.h
nobase_nodist_include_HEADERS = urcu/arch.h urcu/uatomic_arch.h

EXTRA_DIST = $(top_srcdir)/urcu/arch_*.h $(top_srcdir)/urcu/uatomic_arch_*.h gpl-2.0.txt lgpl-2.1.txt lgpl-relicensing.txt README LICENSE

lib_LTLIBRARIES = liburcu.la liburcu-mb.la liburcu-defer.la liburcu-qsbr.la liburcu-bp.la

liburcu_la_SOURCES = urcu.c urcu-pointer.c

liburcu_mb_la_SOURCES = urcu.c urcu-pointer.c
liburcu_mb_la_CFLAGS = -DURCU_MB

liburcu_bp_la_SOURCES = urcu-bp.c urcu-pointer.c

liburcu_defer_la_SOURCES = urcu-defer.c

liburcu_qsbr_la_SOURCES = urcu-qsbr.c urcu-pointer.c

*.h *.c: urcu/arch.h urcu/uatomic_arch.h

urcu/arch.h: $(top_srcdir)/urcu/arch_@ARCHTYPE@.h
	mkdir -p $(top_builddir)/urcu
	cp -f $(top_srcdir)/urcu/arch_@ARCHTYPE@.h $(top_builddir)/urcu/arch.h

urcu/uatomic_arch.h: $(top_srcdir)/urcu/uatomic_arch_@ARCHTYPE@.h
	mkdir -p $(top_builddir)/urcu
	cp -f $(top_srcdir)/urcu/uatomic_arch_@ARCHTYPE@.h $(top_builddir)/urcu/uatomic_arch.h

clean-local:
	rm -f urcu/arch.h urcu/uatomic_arch.h
