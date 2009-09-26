#!/bin/sh
#
# Compiles and runs the urcu.spin Promela model.
#
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
# Copyright (C) IBM Corporation, 2009
#               Mathieu Desnoyers, 2009
#
# Authors: Paul E. McKenney <paulmck@linux.vnet.ibm.com>
#          Mathieu Desnoyers <mathieu.desnoyers@polymtl.ca>

# Basic execution, without LTL clauses. See Makefile.

spin -a mem.spin
cc -DSAFETY -o pan pan.c
./pan -v -c1 -X -m10000000 -w21
