AM_CFLAGS += -I$(top_srcdir)/include -I$(top_builddir)/include -I$(top_srcdir)/src -I$(top_srcdir)/tests/common -g

TEST_EXTENSIONS = .tap
TAP_LOG_DRIVER_FLAGS = --merge --comments
TAP_LOG_DRIVER = env AM_TAP_AWK='$(AWK)' $(SHELL) \
	$(top_srcdir)/config/tap-driver.sh

SCRIPT_LIST = common.sh \
	run-urcu-tests.sh \
	runhash.sh \
	runtests.sh \
	runpaul-phase1.sh \
	runpaul-phase2.sh \
	runpaul-phase3.sh \
	runpaul-phase4.sh \
	runpaul-phase5.sh \
	runpaul-phase6.sh \
	runpaul-phase7.sh \
	runtests-batch.sh \
	subphase4.sh

dist_noinst_SCRIPTS = $(SCRIPT_LIST)

dist_noinst_DATA = \
	hashtable_1_seconds.tap \
	urcu_1_seconds.tap
	hashtable_3_seconds.tap \
	urcu_3_seconds.tap
	hashtable_30_seconds.tap \
	urcu_30_seconds.tap

noinst_PROGRAMS = test_urcu test_urcu_dynamic_link test_urcu_timing \
	test_urcu_signal test_urcu_signal_dynamic_link test_urcu_signal_timing \
        test_rwlock_timing test_rwlock test_perthreadlock_timing \
        test_perthreadlock test_urcu_yield test_urcu_signal_yield test_urcu_mb \
        test_urcu_qsbr_timing test_urcu_qsbr \
	test_mutex test_looplen test_urcu_gc test_urcu_signal_gc \
	test_urcu_lgc \
        test_urcu_mb_gc test_urcu_qsbr_gc test_urcu_qsbr_lgc test_urcu_signal_lgc \
        test_urcu_mb_lgc test_urcu_qsbr_dynamic_link test_urcu_defer \
        test_urcu_assign test_urcu_assign_dynamic_link \
        test_urcu_bp test_urcu_bp_dynamic_link test_cycles_per_loop \
	test_urcu_lfq test_urcu_wfq test_urcu_lfs test_urcu_wfs \
	test_urcu_lfs_rcu \
	test_urcu_wfcq \
	test_urcu_wfq_dynlink test_urcu_wfs_dynlink \
	test_urcu_wfcq_dynlink \
	test_urcu_lfq_dynlink test_urcu_lfs_dynlink test_urcu_hash \
	test_urcu_lfs_rcu_dynlink

URCU_COMMON_LIB=$(top_builddir)/src/liburcu-common.la
URCU_LIB=$(top_builddir)/src/liburcu.la
URCU_QSBR_LIB=$(top_builddir)/src/liburcu-qsbr.la
URCU_MB_LIB=$(top_builddir)/src/liburcu-mb.la
URCU_SIGNAL_LIB=$(top_builddir)/src/liburcu-signal.la
URCU_BP_LIB=$(top_builddir)/src/liburcu-bp.la
URCU_CDS_LIB=$(top_builddir)/src/liburcu-cds.la

DEBUG_YIELD_LIB=$(builddir)/../common/libdebug-yield.la

test_urcu_SOURCES = test_urcu.c
test_urcu_LDADD = $(URCU_LIB)

test_urcu_dynamic_link_SOURCES = test_urcu.c
test_urcu_dynamic_link_LDADD = $(URCU_LIB)
test_urcu_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

test_urcu_timing_SOURCES = test_urcu_timing.c
test_urcu_timing_LDADD = $(URCU_LIB)

test_urcu_yield_SOURCES = test_urcu.c
test_urcu_yield_LDADD = $(URCU_LIB) $(DEBUG_YIELD_LIB)
test_urcu_yield_CFLAGS = -DDEBUG_YIELD $(AM_CFLAGS)


test_urcu_qsbr_SOURCES = test_urcu_qsbr.c
test_urcu_qsbr_LDADD = $(URCU_QSBR_LIB)

test_urcu_qsbr_timing_SOURCES = test_urcu_qsbr_timing.c
test_urcu_qsbr_timing_LDADD = $(URCU_QSBR_LIB)


test_urcu_mb_SOURCES = test_urcu.c
test_urcu_mb_LDADD = $(URCU_MB_LIB)
test_urcu_mb_CFLAGS = -DRCU_MB $(AM_CFLAGS)


test_urcu_signal_SOURCES = test_urcu.c
test_urcu_signal_LDADD = $(URCU_SIGNAL_LIB)
test_urcu_signal_CFLAGS = -DRCU_SIGNAL $(AM_CFLAGS)

test_urcu_signal_dynamic_link_SOURCES = test_urcu.c
test_urcu_signal_dynamic_link_LDADD = $(URCU_SIGNAL_LIB)
test_urcu_signal_dynamic_link_CFLAGS = -DRCU_SIGNAL -DDYNAMIC_LINK_TEST \
					$(AM_CFLAGS)

test_urcu_signal_timing_SOURCES = test_urcu_timing.c
test_urcu_signal_timing_LDADD = $(URCU_SIGNAL_LIB)
test_urcu_signal_timing_CFLAGS= -DRCU_SIGNAL $(AM_CFLAGS)

test_urcu_signal_yield_SOURCES = test_urcu.c
test_urcu_signal_yield_LDADD = $(URCU_SIGNAL_LIB) $(DEBUG_YIELD_LIB)
test_urcu_signal_yield_CFLAGS = -DRCU_SIGNAL -DDEBUG_YIELD $(AM_CFLAGS)

test_rwlock_timing_SOURCES = test_rwlock_timing.c
test_rwlock_timing_LDADD = $(URCU_SIGNAL_LIB)

test_rwlock_SOURCES = test_rwlock.c
test_rwlock_LDADD = $(URCU_SIGNAL_LIB)

test_perthreadlock_timing_SOURCES = test_perthreadlock_timing.c
test_perthreadlock_timing_LDADD = $(URCU_SIGNAL_LIB)

test_perthreadlock_SOURCES = test_perthreadlock.c
test_perthreadlock_LDADD = $(URCU_SIGNAL_LIB)

test_mutex_SOURCES = test_mutex.c

test_looplen_SOURCES = test_looplen.c

test_urcu_gc_SOURCES = test_urcu_gc.c
test_urcu_gc_LDADD = $(URCU_LIB)

test_urcu_signal_gc_SOURCES = test_urcu_gc.c
test_urcu_signal_gc_LDADD = $(URCU_SIGNAL_LIB)
test_urcu_signal_gc_CFLAGS = -DRCU_SIGNAL $(AM_CFLAGS)

test_urcu_mb_gc_SOURCES = test_urcu_gc.c
test_urcu_mb_gc_LDADD = $(URCU_MB_LIB)
test_urcu_mb_gc_CFLAGS = -DRCU_MB $(AM_CFLAGS)

test_urcu_qsbr_gc_SOURCES = test_urcu_qsbr_gc.c
test_urcu_qsbr_gc_LDADD = $(URCU_QSBR_LIB)

test_urcu_qsbr_lgc_SOURCES = test_urcu_qsbr_gc.c
test_urcu_qsbr_lgc_LDADD = $(URCU_QSBR_LIB)
test_urcu_qsbr_lgc_CFLAGS = -DTEST_LOCAL_GC $(AM_CFLAGS)

test_urcu_lgc_SOURCES = test_urcu_gc.c
test_urcu_lgc_LDADD = $(URCU_LIB)
test_urcu_lgc_CFLAGS = -DTEST_LOCAL_GC $(AM_CFLAGS)

test_urcu_signal_lgc_SOURCES = test_urcu_gc.c
test_urcu_signal_lgc_LDADD = $(URCU_SIGNAL_LIB)
test_urcu_signal_lgc_CFLAGS = -DRCU_SIGNAL -DTEST_LOCAL_GC $(AM_CFLAGS)

test_urcu_mb_lgc_SOURCES = test_urcu_gc.c
test_urcu_mb_lgc_LDADD = $(URCU_MB_LIB)
test_urcu_mb_lgc_CFLAGS = -DTEST_LOCAL_GC -DRCU_MB $(AM_CFLAGS)

test_urcu_qsbr_dynamic_link_SOURCES = test_urcu_qsbr.c
test_urcu_qsbr_dynamic_link_LDADD = $(URCU_QSBR_LIB)
test_urcu_qsbr_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

test_urcu_defer_SOURCES = test_urcu_defer.c
test_urcu_defer_LDADD = $(URCU_LIB)

test_cycles_per_loop_SOURCES = test_cycles_per_loop.c

test_urcu_assign_SOURCES = test_urcu_assign.c
test_urcu_assign_LDADD = $(URCU_LIB)

test_urcu_assign_dynamic_link_SOURCES = test_urcu_assign.c
test_urcu_assign_dynamic_link_LDADD = $(URCU_LIB)
test_urcu_assign_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

test_urcu_bp_SOURCES = test_urcu_bp.c
test_urcu_bp_LDADD = $(URCU_BP_LIB)

test_urcu_bp_dynamic_link_SOURCES = test_urcu_bp.c
test_urcu_bp_dynamic_link_LDADD = $(URCU_BP_LIB)
test_urcu_bp_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

test_urcu_lfq_SOURCES = test_urcu_lfq.c
test_urcu_lfq_LDADD = $(URCU_LIB) $(URCU_CDS_LIB)

test_urcu_lfq_dynlink_SOURCES = test_urcu_lfq.c
test_urcu_lfq_dynlink_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)
test_urcu_lfq_dynlink_LDADD = $(URCU_LIB) $(URCU_CDS_LIB)

test_urcu_wfq_SOURCES = test_urcu_wfq.c
test_urcu_wfq_LDADD = $(URCU_COMMON_LIB)

test_urcu_wfq_dynlink_SOURCES = test_urcu_wfq.c
test_urcu_wfq_dynlink_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)
test_urcu_wfq_dynlink_LDADD = $(URCU_COMMON_LIB)

test_urcu_wfcq_SOURCES = test_urcu_wfcq.c
test_urcu_wfcq_LDADD = $(URCU_COMMON_LIB)

test_urcu_wfcq_dynlink_SOURCES = test_urcu_wfcq.c
test_urcu_wfcq_dynlink_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)
test_urcu_wfcq_dynlink_LDADD = $(URCU_COMMON_LIB)

test_urcu_lfs_SOURCES = test_urcu_lfs.c
test_urcu_lfs_LDADD = $(URCU_LIB) $(URCU_CDS_LIB)

test_urcu_lfs_rcu_SOURCES = test_urcu_lfs_rcu.c
test_urcu_lfs_rcu_LDADD = $(URCU_LIB) $(URCU_CDS_LIB)

test_urcu_lfs_dynlink_SOURCES = test_urcu_lfs.c
test_urcu_lfs_dynlink_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)
test_urcu_lfs_dynlink_LDADD = $(URCU_LIB) $(URCU_CDS_LIB)

test_urcu_lfs_rcu_dynlink_SOURCES = test_urcu_lfs_rcu.c
test_urcu_lfs_rcu_dynlink_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)
test_urcu_lfs_rcu_dynlink_LDADD = $(URCU_LIB) $(URCU_CDS_LIB)

test_urcu_wfs_SOURCES = test_urcu_wfs.c
test_urcu_wfs_LDADD = $(URCU_COMMON_LIB)

test_urcu_wfs_dynlink_SOURCES = test_urcu_wfs.c
test_urcu_wfs_dynlink_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)
test_urcu_wfs_dynlink_LDADD = $(URCU_COMMON_LIB)

test_urcu_hash_SOURCES = test_urcu_hash.c test_urcu_hash.h \
		test_urcu_hash_rw.c test_urcu_hash_unique.c
test_urcu_hash_CFLAGS = -DRCU_QSBR $(AM_CFLAGS)
test_urcu_hash_LDADD = $(URCU_QSBR_LIB) $(URCU_COMMON_LIB) $(URCU_CDS_LIB)

all-local:
	@if [ x"$(srcdir)" != x"$(builddir)" ]; then \
		for script in $(SCRIPT_LIST) $(TEST_LIST); do \
			cp -f $(srcdir)/$$script $(builddir); \
		done; \
	fi

clean-local:
	@if [ x"$(srcdir)" != x"$(builddir)" ]; then \
		for script in $(SCRIPT_LIST) $(TEST_LIST); do \
			rm -f $(builddir)/$$script; \
		done; \
	fi

.PHONY: short_bench long_bench regtest

# This empty variable is required to enable the TAP test suite for custom
# targets like 'regtest' while keeping the default 'check' a noop.
TESTS =

SHORT_BENCH_TESTS = urcu_3_seconds.tap hashtable_3_seconds.tap
LONG_BENCH_TESTS = urcu_30_seconds.tap hashtable_30_seconds.tap
REGTEST_TESTS = urcu_1_seconds.tap hashtable_1_seconds.tap

short_bench:
	$(MAKE) $(AM_MAKEFLAGS) check TESTS="$(SHORT_BENCH_TESTS)"

long_bench:
	$(MAKE) $(AM_MAKEFLAGS) check TESTS="$(LONG_BENCH_TESTS)"

regtest:
	$(MAKE) $(AM_MAKEFLAGS) check TESTS="$(REGTEST_TESTS)"
