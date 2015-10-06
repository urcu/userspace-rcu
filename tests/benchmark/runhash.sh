#!/bin/bash

source ../utils/tap.sh

NUM_TESTS=17

plan_tests      ${NUM_TESTS}

diag "Executing Hash table test"

# TODO: missing tests:
# - send kill signals during tests to change the behavior between
#   add/remove/random
# - validate that "nr_leaked" is always 0 in SUMMARY for all tests

# 1st parameter: seconds per test
TIME_UNITS=$1

TESTPROG=./test_urcu_hash

NUM_CPUS="1"
for i in nproc gnproc; do
	NUM_CPUS=$($i 2>/dev/null)
	if [ "$?" -eq "0" ]; then
		break
	else
		NUM_CPUS="1"
	fi
done

#thread multiplier: number of processors divided by 4.
if [[ ${NUM_CPUS} -lt 4 ]]; then
	NUM_CPUS=4	# Floor at 4 due to following assumptions.
fi

THREAD_MUL=$(( ${NUM_CPUS} / 4 ))

EXTRA_PARAMS=-v

# ** test update coherency with single-value table

# rw test, single key, replace and del randomly, 4 threads, auto resize.
# key range: init, lookup, and update: 0 to 0
okx ${TESTPROG} 0 $((4*${THREAD_MUL})) ${TIME_UNITS} -A -s -M 1 -N 1 -O 1 ${EXTRA_PARAMS}

# rw test, single key, add unique and del randomly, 4 threads, auto resize.
# key range: init, lookup, and update: 0 to 0
okx ${TESTPROG} 0 $((4*${THREAD_MUL})) ${TIME_UNITS} -A -u -M 1 -N 1 -O 1 ${EXTRA_PARAMS}

# rw test, single key, replace and del randomly, 2 lookup threads, 2 update threads, auto resize.
# key range: init, lookup, and update: 0 to 0
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A -s -M 1 -N 1 -O 1 ${EXTRA_PARAMS}

# rw test, single key, add and del randomly, 2 lookup threads, 2 update threads, auto resize.
# key range: init, lookup, and update: 0 to 0
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A -M 1 -N 1 -O 1 ${EXTRA_PARAMS}


# ** test updates vs lookups with default table

# rw test, 2 lookup, 2 update threads, add and del randomly, auto resize.
# max 1048576 buckets
# key range: init, lookup, and update: 0 to 999999
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A ${EXTRA_PARAMS}

# rw test, 2 lookup, 2 update threads, add_replace and del randomly, auto resize.
# max 1048576 buckets
# key range: init, lookup, and update: 0 to 999999
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A -s ${EXTRA_PARAMS}

# rw test, 2 lookup, 2 update threads, add_unique and del randomly, auto resize.
# max 1048576 buckets
# key range: init, lookup, and update: 0 to 999999
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A -u ${EXTRA_PARAMS}


# test memory management backends

# rw test, 2 lookup, 2 update threads, add only, auto resize.
# max buckets: 1048576
# key range: init, lookup, and update: 0 to 99999999
# mm backend: "order"
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A -m 1 -n 1048576 -i \
	-M 100000000 -N 100000000 -O 100000000 -B order ${EXTRA_PARAMS}

# rw test, 2 lookup, 2 update threads, add only, auto resize.
# max buckets: 1048576
# key range: init, lookup, and update: 0 to 99999999
# mm backend: "chunk"
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A -m 1 -n 1048576 -i \
	-M 100000000 -N 100000000 -O 100000000 -B chunk ${EXTRA_PARAMS}

# rw test, 2 lookup, 2 update threads, add only, auto resize.
# max buckets: 1048576
# key range: init, lookup, and update: 0 to 99999999
# mm backend: "mmap"
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A -m 1 -n 1048576 -i \
	-M 100000000 -N 100000000 -O 100000000 -B mmap ${EXTRA_PARAMS}


# ** key range tests

# rw test, 2 lookup, 2 update threads, add and del randomly, auto resize.
# max 1048576 buckets
# key range: init, and update: 0 to 999999
# key range: lookup: 1000000 to 1999999
# NOTE: reader threads in this test should never have a successful
# lookup. TODO
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A \
	-R 1000000 ${EXTRA_PARAMS}

# ** small key range

# rw test, 2 lookup, 2 update threads, add and del randomly, auto resize.
# max 1048576 buckets
# key range: init, update, and lookups: 0 to 9
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A \
	-M 10 -N 10 -O 10 ${EXTRA_PARAMS}

# rw test, 2 lookup, 2 update threads, add_unique and del randomly, auto resize.
# max 1048576 buckets
# key range: init, update, and lookups: 0 to 9
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A \
	-M 10 -N 10 -O 10 -u ${EXTRA_PARAMS}

# rw test, 2 lookup, 2 update threads, add_replace and del randomly, auto resize.
# max 1048576 buckets
# key range: init, update, and lookups: 0 to 9
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A \
	-M 10 -N 10 -O 10 -s ${EXTRA_PARAMS}

# ** lookup for known keys

# rw test, 2 lookup, 2 update threads, add_replace and del randomly, auto resize.
# max 1048576 buckets
# lookup range is entirely populated.
# key range: init, and lookups: 0 to 9
# key range: updates: 10 to 19
# NOTE: reader threads in this test should always have successful
# lookups. TODO
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A \
	-M 10 -N 10 -O 10 -R 0 -T 0 -S 10 -k 10 -s ${EXTRA_PARAMS}

# ** Uniqueness test

# rw test, 2 lookup, 2 update threads, add_unique, add_replace and del randomly, auto resize.
# max 1048576 buckets
# asserts that no duplicates are observed by reader threads
# standard length hash chains
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A \
	-U ${EXTRA_PARAMS}

# rw test, 2 lookup, 2 update threads, add_unique, add_replace and del randomly, auto resize.
# max 1048576 buckets
# asserts that no duplicates are observed by reader threads
# create long hash chains: using modulo 4 on keys as hash
okx ${TESTPROG} $((2*${THREAD_MUL})) $((2*${THREAD_MUL})) ${TIME_UNITS} -A \
	-U -C 4 ${EXTRA_PARAMS}
