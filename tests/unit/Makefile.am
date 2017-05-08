AM_CFLAGS += -I$(top_srcdir)/include -I$(top_builddir)/include -I$(top_srcdir)/src -I$(top_srcdir)/tests/utils -I$(top_srcdir)/tests/common -g

SCRIPT_LIST = test_loop run.sh unit_tests

noinst_PROGRAMS = test_uatomic \
	test_urcu_multiflavor \
	test_urcu_multiflavor_dynlink

dist_noinst_SCRIPTS = $(SCRIPT_LIST)

noinst_HEADERS = test_urcu_multiflavor.h

URCU_COMMON_LIB=$(top_builddir)/src/liburcu-common.la
URCU_LIB=$(top_builddir)/src/liburcu.la
URCU_QSBR_LIB=$(top_builddir)/src/liburcu-qsbr.la
URCU_MB_LIB=$(top_builddir)/src/liburcu-mb.la
URCU_SIGNAL_LIB=$(top_builddir)/src/liburcu-signal.la
URCU_BP_LIB=$(top_builddir)/src/liburcu-bp.la
URCU_CDS_LIB=$(top_builddir)/src/liburcu-cds.la
TAP_LIB=$(top_builddir)/tests/utils/libtap.a

test_uatomic_SOURCES = test_uatomic.c
test_uatomic_LDADD = $(URCU_COMMON_LIB) $(TAP_LIB)

test_urcu_multiflavor_SOURCES = test_urcu_multiflavor.c \
	test_urcu_multiflavor-memb.c \
	test_urcu_multiflavor-mb.c \
	test_urcu_multiflavor-signal.c \
	test_urcu_multiflavor-qsbr.c \
	test_urcu_multiflavor-bp.c
test_urcu_multiflavor_LDADD = $(URCU_LIB) $(URCU_MB_LIB) \
	$(URCU_SIGNAL_LIB) $(URCU_QSBR_LIB) $(URCU_BP_LIB) $(TAP_LIB)

test_urcu_multiflavor_dynlink_SOURCES = test_urcu_multiflavor.c \
	test_urcu_multiflavor-memb.c \
	test_urcu_multiflavor-mb.c \
	test_urcu_multiflavor-signal.c \
	test_urcu_multiflavor-qsbr.c \
	test_urcu_multiflavor-bp.c
test_urcu_multiflavor_dynlink_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)
test_urcu_multiflavor_dynlink_LDADD = $(URCU_LIB) $(URCU_MB_LIB) \
	$(URCU_SIGNAL_LIB) $(URCU_QSBR_LIB) $(URCU_BP_LIB) $(TAP_LIB)

all-local:
	@if [ x"$(srcdir)" != x"$(builddir)" ]; then \
		for script in $(SCRIPT_LIST); do \
			cp -f $(srcdir)/$$script $(builddir); \
		done; \
	fi

clean-local:
	@if [ x"$(srcdir)" != x"$(builddir)" ]; then \
		for script in $(SCRIPT_LIST); do \
			rm -f $(builddir)/$$script; \
		done; \
	fi

check-am:
	./run.sh unit_tests
