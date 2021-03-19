AM_CPPFLAGS += -I$(top_srcdir)/src

noinst_LIBRARIES = libtap.a
libtap_a_SOURCES = tap.c tap.h

SCRIPT_LIST = tap.sh tap-driver.sh

dist_check_SCRIPTS = $(SCRIPT_LIST)

all-local:
	@if [ x"$(srcdir)" != x"$(builddir)" ]; then \
		for script in $(SCRIPT_LIST); do \
			cp -f $(srcdir)/$$script $(builddir); \
		done; \
	fi

clean-local:
	@if [ x"$(srcdir)" != x"$(builddir)" ]; then \
		for script in $(SCRIPT_LIST); do \
			rm -f $(builddir)/$$script; \
		done; \
	fi
