SUBDIRS = utils common unit benchmark regression

.PHONY: short_bench long_bench regtest

short_bench:
	cd benchmark && $(MAKE) $(AM_MAKEFLAGS) short_bench
long_bench:
	cd benchmark && $(MAKE) $(AM_MAKEFLAGS) long_bench
regtest:
	cd regression && $(MAKE) $(AM_MAKEFLAGS) regtest
	cd benchmark && $(MAKE) $(AM_MAKEFLAGS) regtest
