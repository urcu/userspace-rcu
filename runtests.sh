#!/bin/sh

for a in test_urcu_gc test_urcu_gc_mb test_urcu test_urcu_mb \
			test_urcu_lgc test_qsbr_lgc test_urcu_lgc_mb \
			test_qsbr test_qsbr_gc test_rwlock test_perthreadlock \
			test_mutex; do
	echo "./${a} $*" | tee -a runall.detail.log
	/usr/bin/time --append --output runall.detail.log ./${a} $*
done

