# Copyright (C) 2013  Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
#
# THIS MATERIAL IS PROVIDED AS IS, WITH ABSOLUTELY NO WARRANTY EXPRESSED
# OR IMPLIED.  ANY USE IS AT YOUR OWN RISK.
#
# Permission is hereby granted to use or copy this program for any
# purpose,  provided the above notices are retained on all copies.
# Permission to modify the code and to distribute modified code is
# granted, provided the above notices are retained, and a notice that
# the code was modified is included with the above copyright notice.

CC = gcc
LIBS = -lurcu-qsbr
CFLAGS = -g -O2 -Wall

# Only necessary when building from the source tree and userspace RCU is
# not installed
ifdef BUILD_EXAMPLES_FROM_TREE
LOCAL_CPPFLAGS += -I../../../urcu/ -I../../../
LIBURCU_QSBR_PATH = ../../../.libs/
override LDFLAGS += -L$(LIBURCU_QSBR_PATH) -Wl,-rpath='$$ORIGIN/$(LIBURCU_QSBR_PATH)'

# Third-party Makefiles have to define these targets to integrate with an
# automake project
EMPTY_AUTOMAKE_TARGETS = distdir install install-data install-exec uninstall \
	install-dvi install-html install-info install-ps install-pdf \
	installdirs check installcheck mostlyclean distclean maintainer-clean \
	dvi pdf ps info tags ctags
.PHONY: $(EMPTY_AUTOMAKE_TARGETS)
$(EMPTY_AUTOMAKE_TARGETS):
endif

all: qsbr-minimal

qsbr-minimal: qsbr-minimal.o
	$(CC) -o $@ $^ $(LDFLAGS) $(LIBS)

qsbr-minimal.o: qsbr-minimal.c
	$(CC) $(CPPFLAGS) $(LOCAL_CPPFLAGS) $(CFLAGS) -c -o $@ $<

.PHONY: clean
clean:
	rm -f *.o qsbr-minimal
