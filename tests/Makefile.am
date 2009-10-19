AM_LDFLAGS=-lpthread
AM_CFLAGS=-I$(top_srcdir) -I$(top_builddir)

noinst_PROGRAMS = test_urcu test_urcu_dynamic_link test_urcu_timing \
        test_rwlock_timing test_rwlock test_perthreadlock_timing \
        test_perthreadlock test_urcu_yield test_urcu_mb \
        test_qsbr_timing test_qsbr rcutorture_urcu \
        rcutorture_urcu_mb rcutorture_urcu_bp rcutorture_qsbr \
	test_mutex test_looplen test_urcu_gc \
        test_urcu_gc_mb test_qsbr_gc test_qsbr_lgc test_urcu_lgc \
        test_urcu_lgc_mb test_qsbr_dynamic_link test_urcu_mb_defer \
        test_uatomic test_urcu_assign test_urcu_assign_dynamic_link \
        test_urcu_bp test_urcu_bp_dynamic_link
noinst_HEADERS = rcutorture.h

if COMPAT_ARCH
COMPAT=$(top_srcdir)/compat_arch_@ARCHTYPE@.c
else
COMPAT=
endif

if COMPAT_FUTEX
COMPAT+=$(top_srcdir)/compat_futex.c
endif

URCU_SIGNAL=$(top_srcdir)/urcu.c $(top_srcdir)/urcu-pointer.c $(COMPAT)
# URCU_SIGNAL_YIELD uses urcu.c but -DDEBUG_YIELD must be defined
URCU_SIGNAL_YIELD=$(top_srcdir)/urcu.c $(top_srcdir)/urcu-pointer.c $(COMPAT)
# URCU_MB uses urcu.c but -DURCU_MB must be defined
URCU_MB=$(top_srcdir)/urcu.c $(top_srcdir)/urcu-pointer.c $(COMPAT)
URCU_BP=$(top_srcdir)/urcu-bp.c $(top_srcdir)/urcu-pointer.c $(COMPAT)
URCU_QSBR=$(top_srcdir)/urcu-qsbr.c $(top_srcdir)/urcu-pointer.c $(COMPAT)
# -DURCU_MB must be defined
URCU_MB_DEFER=$(top_srcdir)/urcu.c $(top_srcdir)/urcu-defer.c $(top_srcdir)/urcu-pointer.c $(COMPAT)

URCU_SIGNAL_LIB=$(top_builddir)/liburcu.la
URCU_MB_LIB=$(top_builddir)/liburcu-mb.la
URCU_BP_LIB=$(top_builddir)/liburcu-bp.la
URCU_QSBR_LIB=$(top_builddir)/liburcu-qsbr.la

if GCC_API
APIHEADER=api_gcc.h
else
APIHEADER=api_@ARCHTYPE@.h
endif

EXTRA_DIST = $(top_srcdir)/tests/api_*.h


test_urcu_SOURCES = test_urcu.c $(URCU_SIGNAL)

test_urcu_dynamic_link_SOURCES = test_urcu.c $(URCU_SIGNAL)
test_urcu_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

test_urcu_timing_SOURCES = test_urcu_timing.c $(URCU_SIGNAL)

test_rwlock_timing_SOURCES = test_rwlock_timing.c $(URCU_SIGNAL)

test_rwlock_SOURCES = test_rwlock.c $(URCU_SIGNAL)

test_perthreadlock_timing_SOURCES = test_perthreadlock_timing.c $(URCU_SIGNAL)

test_perthreadlock_SOURCES = test_perthreadlock.c $(URCU_SIGNAL)

test_urcu_yield_SOURCES = test_urcu.c $(URCU_SIGNAL_YIELD)
test_urcu_yield_CFLAGS = -DDEBUG_YIELD $(AM_CFLAGS)

test_urcu_mb_SOURCES = test_urcu.c $(URCU_MB)
test_urcu_mb_CFLAGS = -DURCU_MB $(AM_CFLAGS)

test_qsbr_timing_SOURCES = test_qsbr_timing.c $(URCU_QSBR)

test_qsbr_SOURCES = test_qsbr.c $(URCU_QSBR)

rcutorture_urcu_SOURCES = urcutorture.c
rcutorture_urcu_CFLAGS = -DTORTURE_URCU_SIGNAL $(AM_CFLAGS)
rcutorture_urcu_LDADD = $(URCU_SIGNAL_LIB)

rcutorture_urcu_mb_SOURCES = urcutorture.c
rcutorture_urcu_mb_CFLAGS = -DTORTURE_URCU_MB $(AM_CFLAGS)
rcutorture_urcu_mb_LDADD = $(URCU_MB_LIB)

rcutorture_qsbr_SOURCES = urcutorture.c
rcutorture_qsbr_CFLAGS = -DTORTURE_QSBR $(AM_CFLAGS)
rcutorture_qsbr_LDADD = $(URCU_QSBR_LIB)

rcutorture_urcu_bp_SOURCES = urcutorture.c
rcutorture_urcu_bp_CFLAGS = -DTORTURE_URCU_BP $(AM_CFLAGS)
rcutorture_urcu_bp_LDADD = $(URCU_BP_LIB)

test_mutex_SOURCES = test_mutex.c $(URCU_SIGNAL)

test_looplen_SOURCES = test_looplen.c

test_urcu_gc_SOURCES = test_urcu_gc.c $(URCU_SIGNAL)

test_urcu_gc_mb_SOURCES = test_urcu_gc.c $(URCU_MB)
test_urcu_gc_mb_CFLAGS = -DURCU_MB $(AM_CFLAGS)

test_qsbr_gc_SOURCES = test_qsbr_gc.c $(URCU_QSBR)

test_qsbr_lgc_SOURCES = test_qsbr_gc.c $(URCU_QSBR)
test_qsbr_lgc_CFLAGS = -DTEST_LOCAL_GC $(AM_CFLAGS)

test_urcu_lgc_SOURCES = test_urcu_gc.c $(URCU_SIGNAL)
test_urcu_lgc_CFLAGS = -DTEST_LOCAL_GC $(AM_CFLAGS)

test_urcu_lgc_mb_SOURCES = test_urcu_gc.c $(URCU_MB)
test_urcu_lgc_mb_CFLAGS = -DTEST_LOCAL_GC -DURCU_MB $(AM_CFLAGS)

test_qsbr_dynamic_link_SOURCES = test_qsbr.c $(URCU_QSBR)
test_qsbr_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

test_urcu_mb_defer_SOURCES = test_urcu_defer.c $(URCU_MB_DEFER)
test_urcu_mb_defer_CFLAGS = -DURCU_MB $(AM_CFLAGS)

test_uatomic_SOURCES = test_uatomic.c $(COMPAT)

test_urcu_assign_SOURCES = test_urcu_assign.c $(URCU_SIGNAL)

test_urcu_assign_dynamic_link_SOURCES = test_urcu_assign.c $(URCU_SIGNAL)
test_urcu_assign_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

test_urcu_bp_SOURCES = test_urcu_bp.c $(URCU_BP)

test_urcu_bp_dynamic_link_SOURCES = test_urcu_bp.c $(URCU_BP)
test_urcu_bp_dynamic_link_CFLAGS = -DDYNAMIC_LINK_TEST $(AM_CFLAGS)

urcutorture.c: api.h

api.h: $(APIHEADER)
	cp -f $(srcdir)/$(APIHEADER) api.h

clean-local:
	rm -f api.h
