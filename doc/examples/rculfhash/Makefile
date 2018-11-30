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
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_add
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_add_unique
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_add_replace
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_del
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_destroy
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_lookup
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_for_each_entry_duplicate

.PHONY: clean
clean:
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_add clean
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_add_unique clean
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_add_replace clean
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_del clean
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_destroy clean
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_lookup clean
	$(AM_V_at)$(MAKE) -f Makefile.cds_lfht_for_each_entry_duplicate clean
