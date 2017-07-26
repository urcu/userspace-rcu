#!/bin/bash

. ../utils/tap.sh
. ./common.sh

NUM_TESTS=15

plan_tests	${NUM_TESTS}

for a in test_urcu_gc test_urcu_signal_gc test_urcu_mb_gc test_urcu_qsbr_gc \
	test_urcu_lgc test_urcu_signal_lgc test_urcu_mb_lgc test_urcu_qsbr_lgc \
	test_urcu test_urcu_signal test_urcu_mb test_urcu_qsbr \
	test_rwlock test_perthreadlock test_mutex; do
	okx ${TEST_TIME_BIN} ./"${a}" "$@" 2>"${TMPFILE}"
	diag "time: $(cat "${TMPFILE}")"
done
