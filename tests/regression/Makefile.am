AM_CFLAGS += -I$(top_srcdir)/include -I$(top_builddir)/include -I$(top_srcdir)/src -I$(top_srcdir)/tests/utils -I$(top_srcdir)/tests/common -g

SCRIPT_LIST = run.sh

dist_noinst_SCRIPTS = $(SCRIPT_LIST)

dist_noinst_DATA = regression_tests.in

noinst_PROGRAMS = test_urcu_fork \
	rcutorture_urcu \
	rcutorture_urcu_signal \
	rcutorture_urcu_mb \
	rcutorture_urcu_bp \
	rcutorture_urcu_qsbr

noinst_HEADERS = rcutorture.h

URCU_COMMON_LIB=$(top_builddir)/src/liburcu-common.la
URCU_LIB=$(top_builddir)/src/liburcu.la
URCU_QSBR_LIB=$(top_builddir)/src/liburcu-qsbr.la
URCU_MB_LIB=$(top_builddir)/src/liburcu-mb.la
URCU_SIGNAL_LIB=$(top_builddir)/src/liburcu-signal.la
URCU_BP_LIB=$(top_builddir)/src/liburcu-bp.la
URCU_CDS_LIB=$(top_builddir)/src/liburcu-cds.la
TAP_LIB=$(top_builddir)/tests/utils/libtap.a

test_urcu_fork_SOURCES = test_urcu_fork.c
test_urcu_fork_LDADD = $(URCU_LIB) $(TAP_LIB)

rcutorture_urcu_SOURCES = urcutorture.c
rcutorture_urcu_CFLAGS = -DRCU_MEMBARRIER $(AM_CFLAGS)
rcutorture_urcu_LDADD = $(URCU_LIB) $(TAP_LIB)

rcutorture_urcu_mb_SOURCES = urcutorture.c
rcutorture_urcu_mb_CFLAGS = -DRCU_MB $(AM_CFLAGS)
rcutorture_urcu_mb_LDADD = $(URCU_MB_LIB)  $(TAP_LIB)

rcutorture_urcu_qsbr_SOURCES = urcutorture.c
rcutorture_urcu_qsbr_CFLAGS = -DTORTURE_QSBR -DRCU_QSBR $(AM_CFLAGS)
rcutorture_urcu_qsbr_LDADD = $(URCU_QSBR_LIB) $(TAP_LIB)

rcutorture_urcu_signal_SOURCES = urcutorture.c
rcutorture_urcu_signal_CFLAGS = -DRCU_SIGNAL $(AM_CFLAGS)
rcutorture_urcu_signal_LDADD = $(URCU_SIGNAL_LIB) $(TAP_LIB)

rcutorture_urcu_bp_SOURCES = urcutorture.c
rcutorture_urcu_bp_CFLAGS = -DRCU_BP $(AM_CFLAGS)
rcutorture_urcu_bp_LDADD = $(URCU_BP_LIB) $(TAP_LIB)

urcutorture.c: ../common/api.h

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

.PHONY: regtest

regtest:
	./run.sh regression_tests
