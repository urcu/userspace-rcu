#!/bin/sh

for a in test_urcu test_urcu_mb test_qsbr test_rwlock test_perthreadlock \
			test_mutex; do
	./${a} $*
done

