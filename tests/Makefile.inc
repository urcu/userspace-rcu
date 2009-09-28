
include ../Makefile.build.inc

ifeq ($(findstring ${ARCHTYPE},"x86 ppc"),)
APIHEADER=api_gcc.h
else
APIHEADER=api_${ARCHTYPE}.h
endif

LIBDIR=..

CFLAGS+=-I${LIBDIR}

URCU_SIGNAL=${LIBDIR}/urcu.o ${LIBDIR}/urcu.h
URCU_SIGNAL_YIELD=${LIBDIR}/urcu-yield.o ${LIBDIR}/urcu.h
URCU_MB=${LIBDIR}/urcu-mb.o ${LIBDIR}/urcu.h
URCU_QSBR=${LIBDIR}/urcu-qsbr.o ${LIBDIR}/urcu-qsbr.h
URCU_MB_DEFER=${LIBDIR}/urcu-mb.o ${LIBDIR}/urcu-defer.o ${LIBDIR}/urcu.h

all: test_urcu test_urcu_dynamic_link test_urcu_timing \
	test_rwlock_timing test_rwlock test_perthreadlock_timing \
	test_perthreadlock test_urcu_yield test_urcu_mb \
	urcu-asm.S test_qsbr_timing test_qsbr urcu-asm.o urcutorture \
	urcutorture-yield test_mutex test_looplen test_urcu_gc \
	test_urcu_gc_mb test_qsbr_gc test_qsbr_lgc test_urcu_lgc \
	test_urcu_lgc_mb test_qsbr_dynamic_link test_urcu_mb_defer \
	test_uatomic

api.h: ${APIHEADER}
	cp -f ${APIHEADER} api.h

test_looplen: test_looplen.c ${LIBDIR}/urcu.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)


test_urcu: test_urcu.c ${URCU_SIGNAL}
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_gc: test_urcu_gc.c ${URCU_SIGNAL}
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_lgc: test_urcu_gc.c ${URCU_SIGNAL}
	$(CC) -DTEST_LOCAL_GC ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)


test_urcu_mb: test_urcu.c ${URCU_MB}
	$(CC) -DURCU_MB ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_gc_mb: test_urcu_gc.c ${URCU_MB}
	$(CC) -DURCU_MB ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_lgc_mb: test_urcu_gc.c ${URCU_MB}
	$(CC) -DTEST_LOCAL_GC -DURCU_MB ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_mb_defer: test_urcu_defer.c ${URCU_MB_DEFER}
	$(CC) -DURCU_MB ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)


test_qsbr: test_qsbr.c ${URCU_QSBR}
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_qsbr_gc: test_qsbr_gc.c ${URCU_QSBR}
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_qsbr_lgc: test_qsbr_gc.c ${URCU_QSBR}
	$(CC) -DTEST_LOCAL_GC ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_qsbr_dynamic_link: test_qsbr.c ${URCU_QSBR}
	$(CC) ${CFLAGS} -DDYNAMIC_LINK_TEST $(LDFLAGS) -o $@ $(SRC_DEP)


test_rwlock: test_rwlock.c ${URCU_SIGNAL}
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_perthreadlock: test_perthreadlock.c ${URCU_SIGNAL}
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_mutex: test_mutex.c ${URCU_SIGNAL}
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_dynamic_link: test_urcu.c ${URCU_SIGNAL}
	$(CC) ${CFLAGS} -DDYNAMIC_LINK_TEST $(LDFLAGS) -o $@ $(SRC_DEP)


test_urcu_yield: test_urcu.c ${URCU_SIGNAL_YIELD}
	$(CC) -DDEBUG_YIELD ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_timing: test_urcu_timing.c ${URCU_SIGNAL}
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_qsbr_timing: test_qsbr_timing.c ${URCU_QSBR}
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_rwlock_timing: test_rwlock_timing.c ${URCU_SIGNAL}
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_perthreadlock_timing: test_perthreadlock_timing.c ${URCU_SIGNAL}
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

urcu-asm.S: urcu-asm.c ${LIBDIR}/urcu.h
	$(CC) ${CFLAGS} -S -o $@ $(SRC_DEP)

urcu-asm.o: urcu-asm.c ${LIBDIR}/urcu.h
	$(CC) ${CFLAGS} -c -o $@ $(SRC_DEP)

urcutorture: urcutorture.c rcutorture.h api.h ${URCU_SIGNAL} 
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

urcutorture-yield: urcutorture.c ${URCU_SIGNAL_YIELD} rcutorture.h api.h
	$(CC) -DDEBUG_YIELD ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_uatomic: test_uatomic.c ../urcu/arch_uatomic.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

,PHONY: clean

clean:
	rm -f *.o test_urcu test_urcu_dynamic_link test_urcu_timing \
	test_rwlock_timing test_rwlock test_perthreadlock_timing \
	test_perthreadlock test_urcu_yield test_urcu_mb \
	urcu-asm.S test_qsbr_timing test_qsbr urcutorture \
	urcutorture-yield liburcu.so api.h \
	test_mutex test_urcu_gc test_urcu_gc_mb urcu-asm-1.S \
	test_qsbr_lgc test_qsbr_gc test_looplen test_urcu_lgc \
	test_urcu_lgc_mb test_qsbr_dynamic_link test_urcu_mb_defer \
	test_uatomic
