AM_CPPFLAGS += -I$(top_srcdir)/src -I$(top_srcdir)/tests/utils -I$(top_srcdir)/tests/common

TEST_EXTENSIONS = .tap
TAP_LOG_DRIVER_FLAGS = --merge --comments
TAP_LOG_DRIVER = env AM_TAP_AWK='$(AWK)' $(SHELL) \
	$(top_srcdir)/tests/utils/tap-driver.sh

noinst_PROGRAMS = test_urcu_fork.tap \
	rcutorture_urcu_membarrier \
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

test_urcu_fork_tap_SOURCES = test_urcu_fork.c
test_urcu_fork_tap_LDADD = $(URCU_LIB) $(TAP_LIB)

rcutorture_urcu_membarrier_SOURCES = urcutorture.c
rcutorture_urcu_membarrier_CFLAGS = -DRCU_MEMBARRIER $(AM_CFLAGS)
rcutorture_urcu_membarrier_LDADD = $(URCU_LIB) $(TAP_LIB)

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

.PHONY: regtest

# This empty variable is required to enable the TAP test suite for custom
# targets like 'regtest' while keeping the default 'check' a noop.
TESTS =

REGTEST_TESTS = test_urcu_fork.tap \
	rcutorture_urcu_bp_perf_global.tap \
	rcutorture_urcu_bp_perf_percpu.tap \
	rcutorture_urcu_bp_perf_perthread.tap \
	rcutorture_urcu_bp_rperf_global.tap \
	rcutorture_urcu_bp_rperf_percpu.tap \
	rcutorture_urcu_bp_rperf_perthread.tap \
	rcutorture_urcu_bp_stress_global.tap \
	rcutorture_urcu_bp_stress_percpu.tap \
	rcutorture_urcu_bp_stress_perthread.tap \
	rcutorture_urcu_bp_uperf_global.tap \
	rcutorture_urcu_bp_uperf_percpu.tap \
	rcutorture_urcu_bp_uperf_perthread.tap \
	rcutorture_urcu_mb_perf_global.tap \
	rcutorture_urcu_mb_perf_percpu.tap \
	rcutorture_urcu_mb_perf_perthread.tap \
	rcutorture_urcu_mb_rperf_global.tap \
	rcutorture_urcu_mb_rperf_percpu.tap \
	rcutorture_urcu_mb_rperf_perthread.tap \
	rcutorture_urcu_mb_stress_global.tap \
	rcutorture_urcu_mb_stress_percpu.tap \
	rcutorture_urcu_mb_stress_perthread.tap \
	rcutorture_urcu_mb_uperf_global.tap \
	rcutorture_urcu_mb_uperf_percpu.tap \
	rcutorture_urcu_mb_uperf_perthread.tap \
	rcutorture_urcu_membarrier_perf_global.tap \
	rcutorture_urcu_membarrier_perf_percpu.tap \
	rcutorture_urcu_membarrier_perf_perthread.tap \
	rcutorture_urcu_membarrier_rperf_global.tap \
	rcutorture_urcu_membarrier_rperf_percpu.tap \
	rcutorture_urcu_membarrier_rperf_perthread.tap \
	rcutorture_urcu_membarrier_stress_global.tap \
	rcutorture_urcu_membarrier_stress_percpu.tap \
	rcutorture_urcu_membarrier_stress_perthread.tap \
	rcutorture_urcu_membarrier_uperf_global.tap \
	rcutorture_urcu_membarrier_uperf_percpu.tap \
	rcutorture_urcu_membarrier_uperf_perthread.tap \
	rcutorture_urcu_qsbr_perf_global.tap \
	rcutorture_urcu_qsbr_perf_percpu.tap \
	rcutorture_urcu_qsbr_perf_perthread.tap \
	rcutorture_urcu_qsbr_rperf_global.tap \
	rcutorture_urcu_qsbr_rperf_percpu.tap \
	rcutorture_urcu_qsbr_rperf_perthread.tap \
	rcutorture_urcu_qsbr_stress_global.tap \
	rcutorture_urcu_qsbr_stress_percpu.tap \
	rcutorture_urcu_qsbr_stress_perthread.tap \
	rcutorture_urcu_qsbr_uperf_global.tap \
	rcutorture_urcu_qsbr_uperf_percpu.tap \
	rcutorture_urcu_qsbr_uperf_perthread.tap \
	rcutorture_urcu_signal_perf_global.tap \
	rcutorture_urcu_signal_perf_percpu.tap \
	rcutorture_urcu_signal_perf_perthread.tap \
	rcutorture_urcu_signal_rperf_global.tap \
	rcutorture_urcu_signal_rperf_percpu.tap \
	rcutorture_urcu_signal_rperf_perthread.tap \
	rcutorture_urcu_signal_stress_global.tap \
	rcutorture_urcu_signal_stress_percpu.tap \
	rcutorture_urcu_signal_stress_perthread.tap \
	rcutorture_urcu_signal_uperf_global.tap \
	rcutorture_urcu_signal_uperf_percpu.tap \
	rcutorture_urcu_signal_uperf_perthread.tap

regtest:
	$(MAKE) $(AM_MAKEFLAGS) check TESTS="$(REGTEST_TESTS)"
