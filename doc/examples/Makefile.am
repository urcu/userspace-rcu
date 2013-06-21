doc_examplesdir = ${docdir}/examples

doc_examples_qsbr_minimaldir = ${doc_examplesdir}/qsbr-minimal

dist_doc_examples_qsbr_minimal_DATA = \
	qsbr-minimal/Makefile \
	qsbr-minimal/qsbr-minimal.c

dist_doc_examples_DATA = \
	Makefile.examples.template

doc_examples_listdir = ${doc_examplesdir}/list

dist_doc_examples_list_DATA = \
	list/Makefile \
	list/Makefile.cds_list_add_rcu \
	list/Makefile.cds_list_add_tail_rcu \
	list/Makefile.cds_list_del_rcu \
	list/Makefile.cds_list_for_each_rcu \
	list/Makefile.cds_list_for_each_entry_rcu \
	list/Makefile.cds_list_replace_rcu \
	list/cds_list_add_rcu.c \
	list/cds_list_add_tail_rcu.c \
	list/cds_list_del_rcu.c \
	list/cds_list_for_each_rcu.c \
	list/cds_list_for_each_entry_rcu.c \
	list/cds_list_replace_rcu.c

doc_examples_wfcqueuedir = ${doc_examplesdir}/wfcqueue

dist_doc_examples_wfcqueue_DATA = \
	wfcqueue/Makefile.cds_wfcq_enqueue \
	wfcqueue/cds_wfcq_enqueue.c

if NO_SHARED
# Don't build examples if shared libraries support was explicitly
# disabled.
else
SUBDIRS_PROXY = qsbr-minimal list wfcqueue

all-local:
	for subdir in $(SUBDIRS_PROXY); do \
		cd $$subdir && $(MAKE) AM_CPPFLAGS="-I../../../urcu/ -I../../../" AM_LDFLAGS='-L../../../.libs/ -Wl,-rpath="$(PWD)/../../.libs/"' $(AM_MAKEFLAGS) all; cd ..; \
	done

clean-local:
	for subdir in $(SUBDIRS_PROXY); do \
		cd $$subdir && $(MAKE) $(AM_MAKEFLAGS) clean; cd ..; \
	done
endif
