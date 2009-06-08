
CFLAGS=-Wall -O2 -g -I.
LDFLAGS=-lpthread

#debug
#CFLAGS=-Wall -g
#CFLAGS+=-DDEBUG_FULL_MB

#Changing the signal number used by the library. SIGUSR1 by default.
#CFLAGS+=-DSIGURCU=SIGUSR2

SRC_DEP=`echo $^ | sed 's/[^ ]*\.h//g'`

all: arch-api test_urcu test_urcu_dynamic_link test_urcu_timing \
	test_rwlock_timing test_perthreadlock_timing test_urcu_yield urcu-asm.S \
	test_qsbr_timing urcu-asm.o urcutorture urcutorture-yield liburcu.so

arch-api: api.h arch.h
	# Run either make pthreads-x86 or make pthreads-ppc prior to build
	# the RCU library. Architecture auto-detectection not implemented
	# in the build system yet.

pthreads-x86: clean
	cp api_x86.h api.h
	cp arch_x86.h arch.h
	cp arch_atomic_x86.h arch_atomic.h

pthreads-ppc: clean
	cp api_ppc.h api.h
	cp arch_ppc.h arch.h
	cp arch_atomic_ppc.h arch_atomic.h

test_urcu: urcu.o test_urcu.c urcu.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_dynamic_link: urcu.o test_urcu.c urcu.h
	$(CC) ${CFLAGS} -DDYNAMIC_LINK_TEST $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_yield: urcu-yield.o test_urcu.c urcu.h
	$(CC) -DDEBUG_YIELD ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_timing: urcu.o test_urcu_timing.c urcu.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_qsbr_timing: urcu-qsbr.o test_qsbr_timing.c urcu-qsbr.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_rwlock_timing: urcu.o test_rwlock_timing.c urcu.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_perthreadlock_timing: urcu.o test_perthreadlock_timing.c urcu.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

urcu.o: urcu.c urcu.h
	$(CC) -fPIC ${CFLAGS} $(LDFLAGS) -c -o $@ $(SRC_DEP)

urcu-qsbr.o: urcu-qsbr.c urcu-qsbr.h
	$(CC) -fPIC ${CFLAGS} $(LDFLAGS) -c -o $@ $(SRC_DEP)

liburcu.so: urcu.o
	$(CC) -fPIC -shared -o $@ $<

urcu-yield.o: urcu.c urcu.h
	$(CC) -DDEBUG_YIELD ${CFLAGS} $(LDFLAGS) -c -o $@ $(SRC_DEP)

urcu-asm.S: urcu-asm.c urcu.h
	$(CC) ${CFLAGS} -S -o $@ $(SRC_DEP)

urcu-asm.o: urcu-asm.c urcu.h
	$(CC) ${CFLAGS} -c -o $@ $(SRC_DEP)

urcutorture: urcutorture.c urcu.o urcu.h rcutorture.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

urcutorture-yield: urcutorture.c urcu-yield.o urcu.h rcutorture.h
	$(CC) -DDEBUG_YIELD ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

.PHONY: clean install arch-api

install: liburcu.so
	cp -f liburcu.so /usr/lib/
	cp -f arch.h arch_atomic.h compiler.h urcu.h urcu-static.h /usr/include/

clean:
	rm -f *.o test_urcu test_urcu_timing test_rwlock_timing urcu-asm.S \
		test_urcu_yield urcutorture urcutorture-yield liburcu.so \
		test_urcu_dynamic_link api.h arch.h arch_atomic.h
