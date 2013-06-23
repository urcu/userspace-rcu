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

all:
	$(MAKE) -C hlist
	$(MAKE) -C list
	$(MAKE) -C urcu-flavors
	$(MAKE) -C wfcqueue
	$(MAKE) -C rculfqueue
	$(MAKE) -C wfstack
	$(MAKE) -C lfstack
	$(MAKE) -C rculfhash

.PHONY: clean
clean:
	$(MAKE) -C hlist clean
	$(MAKE) -C list clean
	$(MAKE) -C urcu-flavors clean
	$(MAKE) -C wfcqueue clean
	$(MAKE) -C rculfqueue clean
	$(MAKE) -C wfstack clean
	$(MAKE) -C lfstack clean
	$(MAKE) -C rculfhash clean
