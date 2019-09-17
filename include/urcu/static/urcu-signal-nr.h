#ifndef _STATIC_URCU_SIGNAL_NR_H
#define _STATIC_URCU_SIGNAL_NR_H

/*
 * static/urcu-signal-nr.h
 *
 * Userspace RCU header.
 *
 * Copyright (c) 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
 * Copyright (c) 2009 Paul E. McKenney, IBM Corporation.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
 *
 * IBM's contributions to this file may be relicensed under LGPLv2 or later.
 */

/*
 * The signal number used by the RCU library can be overridden with
 * -DSIGRCU= when compiling the library.
 * Provide backward compatibility for liburcu 0.3.x SIGURCU.
 */
#ifdef SIGURCU
#define SIGRCU SIGURCU
#endif

#ifndef SIGRCU
#define SIGRCU SIGUSR1
#endif

#endif /* _STATIC_URCU_SIGNAL_NR_H */
