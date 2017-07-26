#!/bin/bash

. ../utils/tap.sh
. ./common.sh

NUM_TESTS=1

plan_tests	${NUM_TESTS}

#for a in test_urcu_gc test_urcu_gc_mb test_urcu_qsbr_gc; do
for a in test_urcu_gc; do
	okx "${TEST_TIME_BIN}" ./"${a}" "$@" 2>"${TMPFILE}"
	diag "time: $(cat "${TMPFILE}")"
done
