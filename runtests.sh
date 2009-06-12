#!/bin/sh

#add urcu mb

for a in test_urcu test_urcu_mb test_qsbr test_rwlock test_perthreadlock \
			test_mutex; do
	./${a} $*
done


#Vary update fraction
#x: vary update fraction from 0 to 0.0001
  #fix number of readers, vary delay between updates
#y: ops/s

echo Execution update fraction test


#Test scalability :
# x: vary number of readers from 0 to num cpus
# y: ops/s
# 0 writer.

echo Executing scalability test

# x: Vary reader C.S. length from 0 to 10us
# y: ops/s
# 8 readers
# 0 writers

echo Executing reader C.S. length test




