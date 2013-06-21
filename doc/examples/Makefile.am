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
	wfcqueue/Makefile \
	wfcqueue/Makefile.cds_wfcq_enqueue \
	wfcqueue/Makefile.cds_wfcq_dequeue \
	wfcqueue/Makefile.cds_wfcq_splice \
	wfcqueue/cds_wfcq_enqueue.c \
	wfcqueue/cds_wfcq_dequeue.c \
	wfcqueue/cds_wfcq_splice.c

doc_examples_wfstackdir = ${doc_examplesdir}/wfstack

dist_doc_examples_wfstack_DATA = \
	wfstack/Makefile \
	wfstack/Makefile.cds_wfs_push \
	wfstack/Makefile.cds_wfs_pop \
	wfstack/Makefile.cds_wfs_pop_all_blocking \
	wfstack/cds_wfs_push.c \
	wfstack/cds_wfs_pop.c \
	wfstack/cds_wfs_pop_all_blocking.c

doc_examples_lfstackdir = ${doc_examplesdir}/lfstack

dist_doc_examples_lfstack_DATA = \
	lfstack/Makefile \
	lfstack/Makefile.cds_lfs_push \
	lfstack/Makefile.cds_lfs_pop_blocking \
	lfstack/Makefile.cds_lfs_pop_all_blocking \
	lfstack/cds_lfs_push.c \
	lfstack/cds_lfs_pop_blocking.c \
	lfstack/cds_lfs_pop_all_blocking.c

if NO_SHARED
# Don't build examples if shared libraries support was explicitly
# disabled.
else
SUBDIRS_PROXY = qsbr-minimal list wfcqueue wfstack

all-local:
	for subdir in $(SUBDIRS_PROXY); do \
		cd $$subdir && $(MAKE) AM_CPPFLAGS="-I../../../urcu/ -I../../../" AM_LDFLAGS='-L../../../.libs/ -Wl,-rpath="$(PWD)/../../.libs/"' $(AM_MAKEFLAGS) all; cd ..; \
	done

clean-local:
	for subdir in $(SUBDIRS_PROXY); do \
		cd $$subdir && $(MAKE) $(AM_MAKEFLAGS) clean; cd ..; \
	done
endif
