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
	$(MAKE) -f Makefile.cds_lfht_add
	$(MAKE) -f Makefile.cds_lfht_add_unique
	$(MAKE) -f Makefile.cds_lfht_add_replace
	$(MAKE) -f Makefile.cds_lfht_del
	$(MAKE) -f Makefile.cds_lfht_destroy
	$(MAKE) -f Makefile.cds_lfht_lookup
	$(MAKE) -f Makefile.cds_lfht_for_each_entry_duplicate

.PHONY: clean
clean:
	$(MAKE) -f Makefile.cds_lfht_add clean
	$(MAKE) -f Makefile.cds_lfht_add_unique clean
	$(MAKE) -f Makefile.cds_lfht_add_replace clean
	$(MAKE) -f Makefile.cds_lfht_del clean
	$(MAKE) -f Makefile.cds_lfht_destroy clean
	$(MAKE) -f Makefile.cds_lfht_lookup clean
	$(MAKE) -f Makefile.cds_lfht_for_each_entry_duplicate clean
