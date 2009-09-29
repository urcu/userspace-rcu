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
#for multi-core verif, 15.5GB shared mem, use files if full
#CFLAGS=-DHASH64 -DMEMLIM=15500 -DNCORE=2
#CFLAGS=-DHASH64 -DCOLLAPSE -DMA=88 -DMEMLIM=15500 -DNCORE=8

#liveness
#CFLAGS=-DHASH64 -DCOLLAPSE -DMA=88
CFLAGS=-DHASH64 -DCOLLAPSE
#CFLAGS=-DHASH64

SPINFILE=urcu.spin

default:
	make urcu_free | tee urcu_free.log
	make urcu_free_no_mb | tee urcu_free_no_mb.log
	make urcu_free_no_rmb | tee urcu_free_no_rmb.log
	make urcu_free_no_wmb | tee urcu_free_no_wmb.log
	make urcu_free_single_flip | tee urcu_free_single_flip.log
	make urcu_progress_writer | tee urcu_progress_writer.log
	make urcu_progress_reader | tee urcu_progress_reader.log
	make urcu_progress_writer_error | tee urcu_progress_writer_error.log
	make asserts | tee asserts.log
	make summary

#show trail : spin -v -t -N pan.ltl input.spin
# after each individual make.

summary:
	@echo
	@echo "Verification summary"
	@grep errors: *.log

asserts: clean
	cat DEFINES > .input.spin
	cat ${SPINFILE} >> .input.spin
	rm -f .input.spin.trail
	spin -a -X .input.spin
	gcc -O2 -w ${CFLAGS} -DSAFETY -o pan pan.c
	./pan -v -c1 -X -m10000000 -w20
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

urcu_free: clean urcu_free_ltl run
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

urcu_free_nested: clean urcu_free_ltl urcu_free_nested_define run
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

urcu_free_nested_define:
	cp urcu_free_nested.define .input.define

urcu_free_no_rmb: clean urcu_free_ltl urcu_free_no_rmb_define run
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

urcu_free_no_rmb_define:
	cp urcu_free_no_rmb.define .input.define

urcu_free_no_wmb: clean urcu_free_ltl urcu_free_no_wmb_define run
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

urcu_free_no_wmb_define:
	cp urcu_free_no_wmb.define .input.define

urcu_free_no_mb: clean urcu_free_ltl urcu_free_no_mb_define run
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

urcu_free_no_mb_define:
	cp urcu_free_no_mb.define .input.define

urcu_free_single_flip: clean urcu_free_ltl urcu_free_single_flip_define run
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

urcu_free_single_flip_define:
	cp urcu_free_single_flip.define .input.define

urcu_free_ltl:
	touch .input.define
	cat .input.define >> pan.ltl
	cat DEFINES >> pan.ltl
	spin -f "!(`cat urcu_free.ltl | grep -v ^//`)" >> pan.ltl

# Progress checks

urcu_progress_writer: clean urcu_progress_writer_ltl \
		urcu_progress_writer_define run_weak_fair
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

urcu_progress_writer_define:
	cp urcu_progress_writer.define .input.define

urcu_progress_writer_ltl:
	touch .input.define
	cat .input.define > pan.ltl
	cat DEFINES >> pan.ltl
	spin -f "!(`cat urcu_progress.ltl | grep -v ^//`)" >> pan.ltl

urcu_progress_reader: clean urcu_progress_reader_ltl \
		urcu_progress_reader_define run_weak_fair
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

urcu_progress_reader_define:
	cp urcu_progress_reader.define .input.define

urcu_progress_reader_ltl:
	touch .input.define
	cat .input.define > pan.ltl
	cat DEFINES >> pan.ltl
	spin -f "!(`cat urcu_progress.ltl | grep -v ^//`)" >> pan.ltl

urcu_progress_writer_error: clean urcu_progress_writer_error_ltl \
		urcu_progress_writer_error_define run_weak_fair
	cp .input.spin $@.spin.input
	-cp .input.spin.trail $@.spin.input.trail

urcu_progress_writer_error_define:
	cp urcu_progress_writer_error.define .input.define

urcu_progress_writer_error_ltl:
	touch .input.define
	cat .input.define > pan.ltl
	cat DEFINES >> pan.ltl
	spin -f "!(`cat urcu_progress.ltl | grep -v ^//`)" >> pan.ltl


run_weak_fair: pan
	./pan -a -f -v -c1 -X -m10000000 -w20

run: pan
	./pan -a -v -c1 -X -m10000000 -w20

pan: pan.c
	gcc -O2 -w ${CFLAGS} -o pan pan.c

pan.c: pan.ltl ${SPINFILE}
	cat .input.define > .input.spin
	cat DEFINES >> .input.spin
	cat ${SPINFILE} >> .input.spin
	rm -f .input.spin.trail
	spin -a -X -N pan.ltl .input.spin

.PHONY: clean default distclean summary
clean:
	rm -f pan* trail.out .input.spin* *.spin.trail .input.define
distclean:
	rm -f *.trail *.input *.log
