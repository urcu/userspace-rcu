AM_LDFLAGS=-lpthread
AM_CFLAGS=-I$(top_srcdir) -I$(top_builddir) -g

noinst_PROGRAMS = test_urcu test_urcu_dynamic_link test_urcu_timing \
	test_urcu_signal test_urcu_signal_dynamic_link test_urcu_signal_timing \
        test_rwlock_timing test_rwlock test_perthreadlock_timing \
        test_perthreadlock test_urcu_yield test_urcu_signal_yield test_urcu_mb \
        test_urcu_qsbr_timing test_urcu_qsbr rcutorture_urcu rcutorture_urcu_signal \
        rcutorture_urcu_mb rcutorture_urcu_bp rcutorture_urcu_qsbr \
	test_mutex test_looplen test_urcu_gc test_urcu_signal_gc \
	test_urcu_lgc \
        test_urcu_mb_gc test_urcu_qsbr_gc test_urcu_qsbr_lgc test_urcu_signal_lgc \
        test_urcu_mb_lgc test_urcu_qsbr_dynamic_link test_urcu_defer \
        test_uatomic test_urcu_assign test_urcu_assign_dynamic_link \
        test_urcu_bp test_urcu_bp_dynamic_link test_cycles_per_loop \
	test_urcu_lfq test_urcu_wfq test_urcu_lfs test_urcu_wfs \
	test_urcu_wfq_dynlink test_urcu_wfs_dynlink \
	test_urcu_lfq_dynlink test_urcu_lfs_dynlink
noinst_HEADERS = rcutorture.h

if COMPAT_ARCH
COMPAT=$(top_srcdir)/compat_arch_@ARCHTYPE@.c
else
COMPAT=
endif

if COMPAT_FUTEX
COMPAT+=$(top_srcdir)/compat_futex.c
endif

URCU=$(top_srcdir)/urcu.c $(top_srcdir)/urcu-pointer.c $(top_srcdir)/wfqueue.c $(COMPAT)
URCU_QSBR=$(top_srcdir)/urcu-qsbr.c $(top_srcdir)/urcu-pointer.c $(top_srcdir)/wfqueue.c $(COMPAT)
# URCU_MB uses urcu.c but -DRCU_MB must be defined
URCU_MB=$(top_srcdir)/urcu.c $(top_srcdir)/urcu-pointer.c $(top_srcdir)/wfqueue.c $(COMPAT)
# URCU_SIGNAL uses urcu.c but -DRCU_SIGNAL must be defined
URCU_SIGNAL=$(top_srcdir)/urcu.c $(top_srcdir)/urcu-pointer.c $(top_srcdir)/wfqueue.c $(COMPAT)
URCU_BP=$(top_srcdir)/urcu-bp.c $(top_srcdir)/urcu-pointer.c $(top_srcdir)/wfqueue.c $(COMPAT)
URCU_DEFER=$(top_srcdir)/urcu.c $(top_srcdir)/urcu-pointer.c $(top_srcdir)/wfqueue.c $(COMPAT)

URCU_COMMON_LIB=$(top_builddir)/liburcu-common.la
URCU_LIB=$(top_builddir)/liburcu.la
URCU_QSBR_LIB=$(top_builddir)/liburcu-qsbr.la
URCU_MB_LIB=$(top_builddir)/liburcu-mb.la
URCU_SIGNAL_LIB=$(top_builddir)/liburcu-signal.la
URCU_BP_LIB=$(top_builddir)/liburcu-bp.la
URCU_CDS_LIB=$(top_builddir)/liburcu-cds.la

EXTRA_DIST = $(top_srcdir)/tests/api.h runall.sh

test_urcu_SOURCES = test_urcu.c $(URCU)

test_urcu_dynamic_link_SOURCES = test_urcu.c $(URCU)
test_urcu_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

test_urcu_timing_SOURCES = test_urcu_timing.c $(URCU)

test_urcu_yield_SOURCES = test_urcu.c $(URCU)
test_urcu_yield_CFLAGS = -DDEBUG_YIELD $(AM_CFLAGS)


test_urcu_qsbr_SOURCES = test_urcu_qsbr.c $(URCU_QSBR)

test_urcu_qsbr_timing_SOURCES = test_urcu_qsbr_timing.c $(URCU_QSBR)


test_urcu_mb_SOURCES = test_urcu.c $(URCU_MB)
test_urcu_mb_CFLAGS = -DRCU_MB $(AM_CFLAGS)


test_urcu_signal_SOURCES = test_urcu.c $(URCU_SIGNAL)
test_urcu_signal_CFLAGS = -DRCU_SIGNAL $(AM_CFLAGS)

test_urcu_signal_dynamic_link_SOURCES = test_urcu.c $(URCU_SIGNAL)
test_urcu_signal_dynamic_link_CFLAGS = -DRCU_SIGNAL -DDYNAMIC_LINK_TEST \
					$(AM_CFLAGS)

test_urcu_signal_timing_SOURCES = test_urcu_timing.c $(URCU_SIGNAL)
test_urcu_signal_timing_CFLAGS= -DRCU_SIGNAL $(AM_CFLAGS)

test_urcu_signal_yield_SOURCES = test_urcu.c $(URCU_SIGNAL)
test_urcu_signal_yield_CFLAGS = -DRCU_SIGNAL -DDEBUG_YIELD $(AM_CFLAGS)


test_rwlock_timing_SOURCES = test_rwlock_timing.c $(URCU_SIGNAL)

test_rwlock_SOURCES = test_rwlock.c $(URCU_SIGNAL)

test_perthreadlock_timing_SOURCES = test_perthreadlock_timing.c $(URCU_SIGNAL)

test_perthreadlock_SOURCES = test_perthreadlock.c $(URCU_SIGNAL)


rcutorture_urcu_SOURCES = urcutorture.c
rcutorture_urcu_CFLAGS = -DRCU_MEMBARRIER $(AM_CFLAGS)
rcutorture_urcu_LDADD = $(URCU)

rcutorture_urcu_mb_SOURCES = urcutorture.c
rcutorture_urcu_mb_CFLAGS = -DRCU_MB $(AM_CFLAGS)
rcutorture_urcu_mb_LDADD = $(URCU_MB_LIB)

rcutorture_urcu_qsbr_SOURCES = urcutorture.c
rcutorture_urcu_qsbr_CFLAGS = -DTORTURE_QSBR -DRCU_QSBR $(AM_CFLAGS)
rcutorture_urcu_qsbr_LDADD = $(URCU_QSBR_LIB)

rcutorture_urcu_signal_SOURCES = urcutorture.c
rcutorture_urcu_signal_CFLAGS = -DRCU_SIGNAL $(AM_CFLAGS)
rcutorture_urcu_signal_LDADD = $(URCU_SIGNAL_LIB)

rcutorture_urcu_bp_SOURCES = urcutorture.c
rcutorture_urcu_bp_CFLAGS = -DRCU_BP $(AM_CFLAGS)
rcutorture_urcu_bp_LDADD = $(URCU_BP_LIB)

test_mutex_SOURCES = test_mutex.c $(URCU)

test_looplen_SOURCES = test_looplen.c

test_urcu_gc_SOURCES = test_urcu_gc.c $(URCU)

test_urcu_signal_gc_SOURCES = test_urcu_gc.c $(URCU_SIGNAL)
test_urcu_signal_gc_CFLAGS = -DRCU_SIGNAL $(AM_CFLAGS)

test_urcu_mb_gc_SOURCES = test_urcu_gc.c $(URCU_MB)
test_urcu_mb_gc_CFLAGS = -DRCU_MB $(AM_CFLAGS)

test_urcu_qsbr_gc_SOURCES = test_urcu_qsbr_gc.c $(URCU_QSBR)

test_urcu_qsbr_lgc_SOURCES = test_urcu_qsbr_gc.c $(URCU_QSBR)
test_urcu_qsbr_lgc_CFLAGS = -DTEST_LOCAL_GC $(AM_CFLAGS)

test_urcu_lgc_SOURCES = test_urcu_gc.c $(URCU)
test_urcu_lgc_CFLAGS = -DTEST_LOCAL_GC $(AM_CFLAGS)

test_urcu_signal_lgc_SOURCES = test_urcu_gc.c $(URCU_SIGNAL)
test_urcu_signal_lgc_CFLAGS = -DRCU_SIGNAL -DTEST_LOCAL_GC $(AM_CFLAGS)

test_urcu_mb_lgc_SOURCES = test_urcu_gc.c $(URCU_MB)
test_urcu_mb_lgc_CFLAGS = -DTEST_LOCAL_GC -DRCU_MB $(AM_CFLAGS)

test_urcu_qsbr_dynamic_link_SOURCES = test_urcu_qsbr.c $(URCU_QSBR)
test_urcu_qsbr_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

test_urcu_defer_SOURCES = test_urcu_defer.c $(URCU_DEFER)

test_uatomic_SOURCES = test_uatomic.c $(COMPAT)

test_cycles_per_loop_SOURCES = test_cycles_per_loop.c

test_urcu_assign_SOURCES = test_urcu_assign.c $(URCU)

test_urcu_assign_dynamic_link_SOURCES = test_urcu_assign.c $(URCU)
test_urcu_assign_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

test_urcu_bp_SOURCES = test_urcu_bp.c $(URCU_BP)

test_urcu_bp_dynamic_link_SOURCES = test_urcu_bp.c $(URCU_BP)
test_urcu_bp_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

test_urcu_lfq_SOURCES = test_urcu_lfq.c $(URCU) $(URCU_CDS_LIB)
test_urcu_lfq_dynlink_SOURCES = test_urcu_lfq.c $(URCU)
test_urcu_lfq_dynlink_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)
test_urcu_lfq_dynlink_LDADD = $(URCU_CDS_LIB)

test_urcu_wfq_SOURCES = test_urcu_wfq.c $(URCU_COMMON_LIB)
test_urcu_wfq_dynlink_SOURCES = test_urcu_wfq.c
test_urcu_wfq_dynlink_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)
test_urcu_wfq_dynlink_LDADD = $(URCU_COMMON_LIB)

test_urcu_lfs_SOURCES = test_urcu_lfs.c $(URCU) $(URCU_CDS_LIB)
test_urcu_lfs_dynlink_SOURCES = test_urcu_lfs.c $(URCU)
test_urcu_lfs_dynlink_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)
test_urcu_lfs_dynlink_LDADD = $(URCU_CDS_LIB)

test_urcu_wfs_SOURCES = test_urcu_wfs.c $(URCU_COMMON_LIB)
test_urcu_wfs_dynlink_SOURCES = test_urcu_wfs.c
test_urcu_wfs_dynlink_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)
test_urcu_wfs_dynlink_LDADD = $(URCU_COMMON_LIB)

urcutorture.c: api.h

check-am:
	./test_uatomic
	./runall.sh
