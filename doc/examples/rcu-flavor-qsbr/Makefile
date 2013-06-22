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
#
# This makefile is purposefully kept simple to support GNU and BSD make.

CC = gcc
LIBS = -lurcu-qsbr
CFLAGS = -g -O2 -Wall
OBJECTS = rcu-flavor-qsbr.o

all: rcu-flavor-qsbr

rcu-flavor-qsbr: $(OBJECTS)
	$(CC) $(CFLAGS) $(LDFLAGS) $(AM_CFLAGS) $(AM_LDFLAGS) \
		$(LIBS) -o $@ $(OBJECTS)

rcu-flavor-qsbr.o: rcu-flavor-qsbr.c
	$(CC) $(CPPFLAGS) $(CFLAGS) $(AM_CPPFLAGS) $(AM_CFLAGS) \
		-c -o $@ $<

.PHONY: clean
clean:
	rm -f *.o rcu-flavor-qsbr
