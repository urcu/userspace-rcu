
include Makefile.build.inc

DIRS=tests

all: checkarch liburcu.so urcu.o \
	liburcu-qsbr.so urcu-qsbr.o \
	liburcu-mb.so urcu-mb.o \
	liburcu-reclaim.so urcu-reclaim.o \
	urcu-yield.o \
	subdirs

checkarch:
ifeq (${ARCHTYPE},)
	@echo "Architecture ${HOSTTYPE} is currently unsupported by liburcu"
	@exit 1
endif

arch.h: arch_${ARCHTYPE}.h
	cp -f arch_${ARCHTYPE}.h arch.h

arch_atomic.h: arch_atomic_${ARCHTYPE}.h
	cp -f arch_atomic_${ARCHTYPE}.h arch_atomic.h

urcu.h: arch.h arch_atomic.h

urcu-qsbr.h: arch.h arch_atomic.h

urcu.o: urcu.c urcu.h
	$(CC) -fPIC ${CFLAGS} $(LDFLAGS) -c -o $@ $(SRC_DEP)

urcu-mb.o: urcu.c urcu.h
	$(CC) -fPIC -DURCU_MB ${CFLAGS} $(LDFLAGS) -c -o $@ $(SRC_DEP)

urcu-qsbr.o: urcu-qsbr.c urcu-qsbr.h
	$(CC) -fPIC ${CFLAGS} $(LDFLAGS) -c -o $@ $(SRC_DEP)

urcu-reclaim.o: urcu-reclaim.c urcu-reclaim.h
	$(CC) -fPIC ${CFLAGS} $(LDFLAGS) -c -o $@ $(SRC_DEP)

liburcu.so: urcu.o
	$(CC) ${LDFLAGS} -fPIC -shared -o $@ $<

liburcu-qsbr.so: urcu-qsbr.o
	$(CC) ${LDFLAGS} -fPIC -shared -o $@ $<

liburcu-mb.so: urcu-mb.o
	$(CC) ${LDFLAGS} -fPIC -shared -o $@ $<

liburcu-reclaim.so: urcu-reclaim.o
	$(CC) ${LDFLAGS} -fPIC -shared -o $@ $<

urcu-yield.o: urcu.c urcu.h
	$(CC) -DDEBUG_YIELD ${CFLAGS} $(LDFLAGS) -c -o $@ $(SRC_DEP)

.PHONY: clean install checkarch tests

subdirs:
	-for d in ${DIRS}; do cd $${d}; ${MAKE} ${MFLAGS} ${EXTRAMFLAGS}; done

install: liburcu.so
	cp -f liburcu.so liburcu-mb.so liburcu-qsbr.so /usr/lib/
	cp -f arch.h arch_atomic.h compiler.h	\
		urcu.h urcu-static.h		\
		urcu-qsbr.h urcu-qsbr-static.h	\
			/usr/include/

clean:
	rm -f *.o *.so arch.h arch_atomic.h
	-for d in ${DIRS}; do cd $${d}; ${MAKE} clean; done
