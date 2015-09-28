#!/bin/bash

source ../utils/tap.sh

NUM_TESTS=103

plan_tests	${NUM_TESTS}

#run all tests
diag "Executing URCU tests"

#set to number of active CPUS
NUM_CPUS=$(nproc)
if [[ ${NUM_CPUS} -lt 4 ]]; then
	NUM_CPUS=4	# Floor at 4 due to following assumptions.
fi

#first parameter: seconds per test
DURATION=$1

#extra options, e.g. for setting affinity on even CPUs :
#EXTRA_OPTS=$(for a in $(seq 0 2 127); do echo -n "-a ${a} "; done)

#ppc64 striding, use with NUM_CPUS=8

#stride 1
#EXTRA_OPTS=$(for a in $(seq 0 2 15); do echo -n "-a ${a} "; done)
#stride 2
#EXTRA_OPTS=$(for a in $(seq 0 4 31); do echo -n "-a ${a} "; done)
#stride 4
#EXTRA_OPTS=$(for a in $(seq 0 8 63); do echo -n "-a ${a} "; done)
#stride 8
#EXTRA_OPTS=$(for a in $(seq 0 16 127); do echo -n "-a ${a} "; done)

#Vary update fraction
#x: vary update fraction from 0 to 0.0001
  #fix number of readers and reader C.S. length, vary delay between updates
#y: ops/s


diag "Executing batch RCU test"

BATCH_ARRAY="1 2 4 8 16 32 64 128 256 512 1024 2048 4096 8192 16384 32768 65536
	     131072 262144"
NR_WRITERS=$((${NUM_CPUS} / 2))

NR_READERS=$((${NUM_CPUS} - ${NR_WRITERS}))
for BATCH_SIZE in ${BATCH_ARRAY}; do
	okx ./runtests-batch.sh ${NR_READERS} ${NR_WRITERS} ${DURATION} -d 0 -b ${BATCH_SIZE} ${EXTRA_OPTS}
done

#setting gc each 32768. ** UPDATE FOR YOUR ARCHITECTURE BASED ON TEST ABOVE **
EXTRA_OPTS="${EXTRA_OPTS} -b 32768"

diag "Executing update fraction test"

WDELAY_ARRAY="0 1 2 4 8 16 32 64 128 256 512 1024 2048 4096 8192 16384 32768
              65536 131072 262144 524288 1048576 2097152 4194304 8388608
              16777216 33554432 67108864 134217728"
NR_WRITERS=$((${NUM_CPUS} / 2))

NR_READERS=$((${NUM_CPUS} - ${NR_WRITERS}))
for WDELAY in ${WDELAY_ARRAY}; do
	okx ./runtests.sh ${NR_READERS} ${NR_WRITERS} ${DURATION} -d ${WDELAY} ${EXTRA_OPTS}
done

#Test scalability :
# x: vary number of readers from 0 to num cpus
# y: ops/s
# 0 writer.

diag "Executing scalability test"

NR_WRITERS=0

for NR_READERS in $(seq 1 ${NUM_CPUS}); do
	okx ./runtests.sh ${NR_READERS} ${NR_WRITERS} ${DURATION} ${EXTRA_OPTS}
done


# x: Vary reader C.S. length from 0 to 100 us
# y: ops/s
# 8 readers
# 0 writers

diag "Executing reader C.S. length test"

NR_READERS=${NUM_CPUS}
NR_WRITERS=0
#in loops.
READERCSLEN_ARRAY="0 1 2 4 8 16 32 64 128 256 512 1024 2048 4096 8192 16384 32768 65536 131072 262144 524288 1048576 2097152"

for READERCSLEN in ${READERCSLEN_ARRAY}; do
	okx ./runtests.sh ${NR_READERS} ${NR_WRITERS} ${DURATION} ${EXTRA_OPTS} -c ${READERCSLEN}
done
