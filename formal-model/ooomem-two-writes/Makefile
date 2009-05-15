# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
#
# Copyright (C) Mathieu Desnoyers, 2009
#
# Authors: Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>

#CFLAGS=-DSAFETY
#CFLAGS=-DHASH64 -DREACH
CFLAGS=-DHASH64

#try pan -i to get the smallest trace.

SPINFILE=mem.spin

default:
	make read_order | tee read_order.log
	make read_order_no_wmb | tee read_order_no_wmb.log
	make read_order_no_rmb | tee read_order_no_rmb.log
	make read_order_no_sync | tee read_order_no_sync.log
	make asserts | tee asserts.log
	make summary

#show trail : spin -v -t -N pan.ltl input.spin
# after each individual make.

summary:
	@echo
	@echo "Verification summary"
	@grep error *.log

asserts: clean
	cat DEFINES > .input.spin
	cat ${SPINFILE} >> .input.spin
	rm -f .input.spin.trail
	spin -a -X .input.spin
	gcc -w ${CFLAGS} -DSAFETY -o pan pan.c
	./pan -v -c1 -X -m10000 -w19
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

read_order: clean read_order_ltl run
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

read_order_no_sync: clean read_order_ltl read_order_no_sync_define run
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

read_order_no_sync_define:
	cp read_order_no_sync.define .input.define

read_order_no_rmb: clean read_order_ltl read_order_no_rmb_define run
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

read_order_no_rmb_define:
	cp read_order_no_rmb.define .input.define

read_order_no_wmb: clean read_order_ltl read_order_no_wmb_define run
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

read_order_no_wmb_define:
	cp read_order_no_wmb.define .input.define

read_order_ltl:
	touch .input.define
	cat DEFINES > pan.ltl
	cat .input.define >> pan.ltl
	spin -f "!(`cat read_order.ltl | grep -v ^//`)" >> pan.ltl

run: pan
	./pan -a -v -c1 -X -m10000 -w19

pan: pan.c
	gcc -w ${CFLAGS} -o pan pan.c

pan.c: pan.ltl ${SPINFILE}
	cat DEFINES > .input.spin
	cat .input.define >> .input.spin
	cat ${SPINFILE} >> .input.spin
	rm -f .input.spin.trail
	spin -a -X -N pan.ltl .input.spin

.PHONY: clean default distclean summary
clean:
	rm -f pan* trail.out .input.spin* *.spin.trail .input.define
distclean:
	rm -f *.trail *.input *.log
