
include Makefile.build.inc

DIRS=tests

all: checkarch liburcu.so urcu.o \
	liburcu-qsbr.so urcu-qsbr.o \
	liburcu-mb.so urcu-mb.o \
	liburcu-bp.so urcu-bp.o \
	liburcu-defer.so urcu-defer.o \
	urcu-yield.o \
	subdirs

checkarch:
ifeq (${ARCHTYPE},)
	@echo "Architecture ${HOSTTYPE} is currently unsupported by liburcu"
	@exit 1
endif

urcu/arch.h: urcu/arch_${ARCHTYPE}.h
	cp -f urcu/arch_${ARCHTYPE}.h urcu/arch.h

urcu/arch_uatomic.h: urcu/arch_uatomic_${ARCHTYPE}.h
	cp -f urcu/arch_uatomic_${ARCHTYPE}.h urcu/arch_uatomic.h

urcu.h: urcu/arch.h urcu/arch_uatomic.h

urcu-qsbr.h: urcu/arch.h urcu/arch_uatomic.h

urcu-pointer.o: urcu-pointer.c urcu-pointer.h urcu-pointer-static.h
	$(CC) -fPIC ${CFLAGS} -c -o $@ $(SRC_DEP)

urcu.o: urcu.c urcu.h
	$(CC) -fPIC ${CFLAGS} -c -o $@ $(SRC_DEP)

urcu-mb.o: urcu.c urcu.h
	$(CC) -fPIC -DURCU_MB ${CFLAGS} -c -o $@ $(SRC_DEP)

urcu-bp.o: urcu-bp.c urcu-bp.h
	$(CC) -fPIC ${CFLAGS} -c -o $@ $(SRC_DEP)

urcu-qsbr.o: urcu-qsbr.c urcu-qsbr.h
	$(CC) -fPIC ${CFLAGS} -c -o $@ $(SRC_DEP)

urcu-defer.o: urcu-defer.c urcu-defer.h
	$(CC) -fPIC ${CFLAGS} -c -o $@ $(SRC_DEP)

liburcu.so: urcu.o urcu-pointer.o
	$(CC) ${LDFLAGS} -fPIC -shared -o $@ $<

liburcu-qsbr.so: urcu-qsbr.o urcu-pointer.o
	$(CC) ${LDFLAGS} -fPIC -shared -o $@ $<

liburcu-mb.so: urcu-mb.o urcu-pointer.o
	$(CC) ${LDFLAGS} -fPIC -shared -o $@ $<

liburcu-bp.so: urcu-bp.o urcu-pointer.o
	$(CC) ${LDFLAGS} -fPIC -shared -o $@ $<

liburcu-defer.so: urcu-defer.o
	$(CC) ${LDFLAGS} -fPIC -shared -o $@ $<

urcu-yield.o: urcu.c urcu.h
	$(CC) -DDEBUG_YIELD ${CFLAGS} -c -o $@ $(SRC_DEP)

.PHONY: clean install checkarch tests

subdirs:
	-for d in ${DIRS}; do cd $${d}; ${MAKE} ${MFLAGS} ${EXTRAMFLAGS}; done

install: liburcu.so
	cp -f liburcu.so liburcu-mb.so liburcu-qsbr.so liburcu-defer.so	\
		liburcu-bp.so 						\
			/usr/lib/
	mkdir -p /usr/include/urcu
	cp -f urcu/arch.h urcu/arch_uatomic.h urcu/compiler.h		\
		urcu/system.h urcu/list.h urcu/rculist.h urcu/hlist.h	\
			/usr/include/urcu/
	cp -f urcu.h urcu-static.h					\
		urcu-qsbr.h urcu-qsbr-static.h				\
		urcu-bp.h urcu-bp-static.h				\
		urcu-defer.h urcu-defer-static.h			\
		urcu-pointer.h urcu-pointer-static.h			\
			/usr/include/

clean:
	rm -f *.o *.so urcu/arch.h urcu/arch_uatomic.h
	-for d in ${DIRS}; do cd $${d}; ${MAKE} clean; done
