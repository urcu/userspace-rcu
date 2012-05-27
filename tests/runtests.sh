#!/bin/sh

for a in test_urcu_gc test_urcu_signal_gc test_urcu_mb_gc test_urcu_qsbr_gc \
	test_urcu_lgc test_urcu_signal_lgc test_urcu_mb_lgc test_urcu_qsbr_lgc \
	test_urcu test_urcu_signal test_urcu_mb test_urcu_qsbr \
	test_rwlock test_perthreadlock test_mutex; do
	echo "./${a} $*" | tee -a runall.detail.log
	/usr/bin/time -a -o runall.detail.log ./${a} $*
done

