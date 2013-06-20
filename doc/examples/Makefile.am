doc_examplesdir = ${docdir}/examples

doc_examples_qsbr_minimaldir = ${doc_examplesdir}/qsbr-minimal

dist_doc_examples_qsbr_minimal_DATA = \
	qsbr-minimal/Makefile \
	qsbr-minimal/qsbr-minimal.c

if NO_SHARED
# Don't build examples if shared libraries support was explicitly
# disabled.
else
SUBDIRS_PROXY = qsbr-minimal

all-local:
	for subdir in $(SUBDIRS_PROXY); do \
		cd $$subdir && $(MAKE) AM_CPPFLAGS="-I../../../urcu/ -I../../../" AM_LDFLAGS='-L../../../.libs/ -Wl,-rpath="$(PWD)/../../.libs/"' $(AM_MAKEFLAGS) all; cd ..; \
	done

clean-local:
	for subdir in $(SUBDIRS_PROXY); do \
		cd $$subdir && $(MAKE) $(AM_MAKEFLAGS) clean; cd ..; \
	done
endif
