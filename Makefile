
CFLAGS=-Wall -O2
#debug
#CFLAGS=-Wall -g
LDFLAGS=-lpthread

SRC_DEP=`echo $^ | sed 's/[^ ]*.h//g'`

all: test_urcu test_urcu_timing test_rwlock_timing test_urcu_yield urcu-asm.S \
	urcu-asm.o

test_urcu: urcu.o test_urcu.c urcu.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_yield: urcu-yield.o test_urcu.c urcu.h
	$(CC) -DDEBUG_YIELD ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_urcu_timing: urcu.o test_urcu_timing.c urcu.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

test_rwlock_timing: urcu.o test_rwlock_timing.c urcu.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

urcu.o: urcu.c urcu.h
	$(CC) ${CFLAGS} $(LDFLAGS) -c -o $@ $(SRC_DEP)

urcu-yield.o: urcu.c urcu.h
	$(CC) -DDEBUG_YIELD ${CFLAGS} $(LDFLAGS) -c -o $@ $(SRC_DEP)

urcu-asm.S: urcu-asm.c urcu.h
	$(CC) ${CFLAGS} -S -o $@ $(SRC_DEP)

urcu-asm.o: urcu-asm.c urcu.h
	$(CC) ${CFLAGS} -c -o $@ $(SRC_DEP)

#in progress...
urcutorture: urcutorture.c urcu.o urcu.h rcutorture.h
	$(CC) ${CFLAGS} $(LDFLAGS) -o $@ $(SRC_DEP)

.PHONY: clean

clean:
	rm -f *.o test_urcu test_urcu_timing test_rwlock_timing urcu-asm.S \
		test_urcu_yield
