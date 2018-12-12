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
	$(AM_V_at)$(MAKE) -C hlist
	$(AM_V_at)$(MAKE) -C list
	$(AM_V_at)$(MAKE) -C urcu-flavors
	$(AM_V_at)$(MAKE) -C wfcqueue
	$(AM_V_at)$(MAKE) -C rculfqueue
	$(AM_V_at)$(MAKE) -C wfstack
	$(AM_V_at)$(MAKE) -C lfstack
	$(AM_V_at)$(MAKE) -C rculfhash

.PHONY: clean
clean:
	$(AM_V_at)$(MAKE) -C hlist clean
	$(AM_V_at)$(MAKE) -C list clean
	$(AM_V_at)$(MAKE) -C urcu-flavors clean
	$(AM_V_at)$(MAKE) -C wfcqueue clean
	$(AM_V_at)$(MAKE) -C rculfqueue clean
	$(AM_V_at)$(MAKE) -C wfstack clean
	$(AM_V_at)$(MAKE) -C lfstack clean
	$(AM_V_at)$(MAKE) -C rculfhash clean
