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
SPINFILE_FAIR=mem-progress.spin

default:
	make refcount | tee refcount.log
	make refcount_4_bits_per_byte | tee refcount_4_bits_per_byte.log
	make lock_progress | tee lock_progress.log
	make lock_progress_4_bits_per_byte | tee lock_progress_4_bits_per_byte.log
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
	./pan -v -c1 -X -m10000000 -w19
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

refcount: clean refcount_ltl run
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

refcount_ltl:
	touch .input.define
	cat DEFINES > pan.ltl
	cat .input.define >> pan.ltl
	spin -f "!(`cat refcount.ltl | grep -v ^//`)" >> pan.ltl

refcount_4_bits_per_byte: clean refcount_ltl config_4_bits_per_byte_define run

lock_progress: clean lock_progress_ltl run_weak_fair
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

lock_progress_ltl:
	touch .input.define
	cat .input.define > pan.ltl
	cat DEFINES >> pan.ltl
	spin -f "!(`cat lock_progress.ltl | grep -v ^//`)" >> pan.ltl

lock_progress_4_bits_per_byte: clean lock_progress_ltl config_4_bits_per_byte_define run

config_4_bits_per_byte_define:
	cp config_4_bits_per_byte.define .input.define

run: pan
	./pan -a -v -c1 -X -m1000000 -w19

run_weak_fair: pan_fair
	./pan_fair -a -f -v -c1 -X -m1000000 -w20

pan_fair: pan_fair.c
	gcc -w ${CFLAGS} -DNFAIR=4 -o pan_fair pan_fair.c

pan: pan.c
	gcc -w ${CFLAGS} -o pan pan.c

pan_fair.c: pan.ltl ${SPINFILE_FAIR}
	cat DEFINES > .input.spin
	cat .input.define >> .input.spin
	cat ${SPINFILE_FAIR} >> .input.spin
	rm -f .input.spin.trail
	spin -a -X -N pan.ltl .input.spin
	mv pan.c pan_fair.c

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
