#!/bin/sh

#for a in test_urcu_gc test_urcu_gc_mb test_urcu_qsbr_gc; do
for a in test_urcu_gc; do
	echo "./${a} $*" | tee -a runall.detail.log
	/usr/bin/time -a -o runall.detail.log ./${a} $*
done

