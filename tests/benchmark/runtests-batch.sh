#!/bin/bash

source ../utils/tap.sh

NUM_TESTS=1

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

tmpfile=$(mktemp)

#for a in test_urcu_gc test_urcu_gc_mb test_urcu_qsbr_gc; do
for a in test_urcu_gc; do
	okx $time_command -o $tmpfile ./${a} $*
	diag "time: $(cat $tmpfile)"
done
