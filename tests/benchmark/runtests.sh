#!/bin/bash

source ../utils/tap.sh

NUM_TESTS=15

plan_tests	${NUM_TESTS}

. ./common.sh

function cleanup()
{
	if [ x"$tmpfile" != x"" ]; then
		rm -f $tmpfile
	fi
}

tmpfile=
trap cleanup SIGINT SIGTERM EXIT
tmpfile=$(mktemp)

# Check if time bin is non-empty
if [ -n "$test_time_bin" ]; then
	time_command="$test_time_bin"
else
	time_command=""
fi

for a in test_urcu_gc test_urcu_signal_gc test_urcu_mb_gc test_urcu_qsbr_gc \
	test_urcu_lgc test_urcu_signal_lgc test_urcu_mb_lgc test_urcu_qsbr_lgc \
	test_urcu test_urcu_signal test_urcu_mb test_urcu_qsbr \
	test_rwlock test_perthreadlock test_mutex; do
	okx $time_command -o $tmpfile ./${a} $*
	diag "time: $(cat $tmpfile)"
done
