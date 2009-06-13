#!/bin/sh

#run all tests

#set to number of active CPUS
NUM_CPUS=8

#extra options, e.g. for setting affinity on even CPUs :
#EXTRA_OPTS=$(for a in $(seq 0 2 63); do echo -n "-a ${a} "; done)


#Vary update fraction
#x: vary update fraction from 0 to 0.0001
  #fix number of readers and reader C.S. length, vary delay between updates
#y: ops/s

echo Executing update fraction test

DURATION=10
WDELAY_ARRAY="0 1 2 4 8 16 32 64 128 256 512 1024 2048 4096 8192 16384 32768
              65536 131072 262144 524288 1048576 2097152 4194304 8388608
              16777216 33554432 67108864 134217728"
NR_WRITERS=$((${NUM_CPUS} / 2))

rm -f update-fraction.log

NR_READERS=$((${NUM_CPUS} - ${NR_WRITERS}))
for WDELAY in ${WDELAY_ARRAY}; do
	./runtests.sh ${NR_READERS} ${NR_WRITERS} ${DURATION} -d ${WDELAY} ${EXTRA_OPTS} | tee -a update-fraction.log
done

#Test scalability :
# x: vary number of readers from 0 to num cpus
# y: ops/s
# 0 writer.

echo Executing scalability test

NR_WRITERS=0
DURATION=10

rm -f scalability.log

for NR_READERS in $(seq 1 ${NUM_CPUS}); do
	./runtests.sh ${NR_READERS} ${NR_WRITERS} ${DURATION} ${EXTRA_OPTS}| tee -a scalability.log
done


# x: Vary reader C.S. length from 0 to 100 us
# y: ops/s
# 8 readers
# 0 writers

echo Executing reader C.S. length test

NR_READERS=${NUM_CPUS}
NR_WRITERS=0
DURATION=10
#in loops.
READERCSLEN_ARRAY="0 1 2 4 8 16 32 64 128 256 512 1024 2048 4096 8192 16384 32768 65536 131072 262144 524288 1048576 2097152"

rm -f readercslen.log

for READERCSLEN in ${READERCSLEN_ARRAY}; do
	./runtests.sh ${NR_READERS} ${NR_WRITERS} ${DURATION} ${EXTRA_OPTS} -c ${READERCSLEN} | tee -a readercslen.log
done
