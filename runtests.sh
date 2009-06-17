#!/bin/sh

for a in test_urcu test_urcu_mb test_qsbr test_rwlock test_perthreadlock \
			test_mutex; do
	echo "./${a} $*" | tee -a runall.detail.log
	/usr/bin/time --append --output runall.detail.log ./${a} $*
done

