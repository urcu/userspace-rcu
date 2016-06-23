ACLOCAL_AMFLAGS=-I m4

SUBDIRS = include src doc tests

dist_doc_DATA = LICENSE \
		README.md

dist_noinst_DATA = CodingStyle

EXTRA_DIST = gpl-2.0.txt \
	lgpl-2.1.txt \
	lgpl-relicensing.txt

.PHONY: short_bench long_bench regtest
short_bench:
	cd tests && $(MAKE) $(AM_MAKEFLAGS) short_bench
long_bench:
	cd tests && $(MAKE) $(AM_MAKEFLAGS) long_bench
regtest:
	cd tests && $(MAKE) $(AM_MAKEFLAGS) regtest
