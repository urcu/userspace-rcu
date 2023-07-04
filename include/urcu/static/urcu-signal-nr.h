// SPDX-FileCopyrightText: 2009 Mathieu Desnoyers <mathieu.desnoyers@efficios.com>
// SPDX-FileCopyrightText: 2009 Paul E. McKenney, IBM Corporation.
//
// SPDX-License-Identifier: LGPL-2.1-or-later

#ifndef _STATIC_URCU_SIGNAL_NR_H
#define _STATIC_URCU_SIGNAL_NR_H

/*
 * Userspace RCU header.
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
