Userspace RCU Implementation
============================

by Mathieu Desnoyers and Paul E. McKenney


Building
--------

    ./bootstrap # skip if using tarball
    ./configure
    make
    make install
    ldconfig

Hints:

  - Forcing 32-bit build:

        CFLAGS="-m32 -g -O2" ./configure

  - Forcing 64-bit build:

        CFLAGS="-m64 -g -O2" ./configure

  - Forcing a 32-bit build with 386 backward compatibility:

        CFLAGS="-m32 -g -O2" ./configure --host=i386-pc-linux-gnu

  - Forcing a 32-bit build for Sparcv9 (typical for Sparc v9)

        CFLAGS="-m32 -Wa,-Av9a -g -O2" ./configure


Architectures supported
-----------------------

Currently, the following architectures are supported:

  - Linux x86 (i386, i486, i586, i686)
  - x86 64-bit
  - PowerPC 32/64
  - S390, S390x
  - ARM 32/64
  - MIPS
  - Alpha
  - ia64
  - Sparcv9 32/64
  - Tilera
  - hppa/PA-RISC

Tested on Linux, FreeBSD 8.2/8.3/9.0/9.1/10.0 i386/amd64, and Cygwin.
Should also work on:

  - Android
  - NetBSD 5
  - OpenBSD
  - Darwin

(more testing needed before claiming support for these OS).

Linux ARM depends on running a Linux kernel 2.6.15 or better, GCC 4.4 or
better.

The GCC compiler versions 3.3, 3.4, 4.0, 4.1, 4.2, 4.3, 4.4 and 4.5 are
supported, with the following exceptions:

  - GCC 3.3 and 3.4 have a bug that prevents them from generating volatile
    accesses to offsets in a TLS structure on 32-bit x86. These versions are
    therefore not compatible with `liburcu` on x86 32-bit
    (i386, i486, i586, i686).
    The problem has been reported to the GCC community:
    http://www.mail-archive.com/gcc-bugs@gcc.gnu.org/msg281255.html
  - GCC 3.3 cannot match the "xchg" instruction on 32-bit x86 build.
    See http://kerneltrap.org/node/7507
  - Alpha, ia64 and ARM architectures depend on GCC 4.x with atomic builtins
    support. For ARM this was introduced with GCC 4.4:
    http://gcc.gnu.org/gcc-4.4/changes.html.

Clang version 3.0 (based on LLVM 3.0) is supported.

Building on MacOS X (Darwin) requires a work-around for processor
detection:

  - 32-bit:

        ./configure --build=i686-apple-darwin11

  - 64-bit:

        ./configure --build=x86_64-apple-darwin11

For developers using the Git tree:

This source tree is based on the autotools suite from GNU to simplify
portability. Here are some things you should have on your system in order to
compile the git repository tree :

  - GNU autotools (automake >=1.10, autoconf >=2.50, autoheader >=2.50)
    (make sure your system wide `automake` points to a recent version!)
  - GNU Libtool >=2.2
    (for more information, go to http://www.gnu.org/software/autoconf/)

If you get the tree from the repository, you will need to use the `bootstrap`
script in the root of the tree. It calls all the GNU tools needed to prepare
the tree configuration.

Test scripts provided in the `tests/` directory of the source tree depend
on `bash` and the `seq` program.


API
---

See the relevant API documentation files in `doc/`. The APIs provided by
Userspace RCU are, by prefix:

  - `rcu_`: Read-Copy Update (see [`doc/rcu-api.md`](doc/rcu-api.md))
  - `cmm_`: Concurrent Memory Model
  - `caa_`: Concurrent Architecture Abstraction
  - `cds_`: Concurrent Data Structures
    (see [`doc/cds-api.md`](doc/cds-api.md))
  - `uatomic_`: Userspace Atomic
    (see [`doc/uatomic-api.md`](doc/uatomic-api.md))


Quick start guide
-----------------

### Usage of all urcu libraries:

  - Define `_LGPL_SOURCE` (only) if your code is LGPL or GPL compatible
    before including the `urcu.h` or `urcu-qsbr.h` header. If your application
    is distributed under another license, function calls will be generated
    instead of inlines, so your application can link with the library.
  - Linking with one of the libraries below is always necessary even for
    LGPL and GPL applications.
  - Define `URCU_INLINE_SMALL_FUNCTIONS` before including Userspace RCU
    headers if you want Userspace RCU to inline small functions (10
    lines or less) into the application. It can be used by applications
    distributed under any kind of license, and does *not* make the
    application a derived work of Userspace RCU.

Those small inlined functions are guaranteed to match the library
content as long as the library major version is unchanged.
Therefore, the application *must* be compiled with headers matching
the library major version number. Applications using
`URCU_INLINE_SMALL_FUNCTIONS` may be unable to use debugging
features of Userspace RCU without being recompiled.


### Usage of `liburcu`

  1. `#include <urcu.h>`
  2. Link the application with `-lurcu`

This is the preferred version of the library, in terms of
grace-period detection speed, read-side speed and flexibility.
Dynamically detects kernel support for `sys_membarrier()`. Falls back
on `urcu-mb` scheme if support is not present, which has slower
read-side.


### Usage of `liburcu-qsbr`

  1. `#include <urcu-qsbr.h>`
  2. Link with `-lurcu-qsbr`

The QSBR flavor of RCU needs to have each reader thread executing
`rcu_quiescent_state()` periodically to progress. `rcu_thread_online()`
and `rcu_thread_offline()` can be used to mark long periods for which
the threads are not active. It provides the fastest read-side at the
expense of more intrusiveness in the application code.


### Usage of `liburcu-mb`

  1. `#include <urcu.h>`
  2. Compile any `_LGPL_SOURCE` code using this library with `-DRCU_MB`
  3. Link with `-lurcu-mb`

This version of the urcu library uses memory barriers on the writer
and reader sides. This results in faster grace-period detection, but
results in slower reads.


### Usage of `liburcu-signal`

  1. `#include <urcu.h>`
  2. Compile any `_LGPL_SOURCE` code using this library with `-DRCU_SIGNAL`
  3. Link the application with `-lurcu-signal`

Version of the library that requires a signal, typically `SIGUSR1`. Can
be overridden with `-DSIGRCU` by modifying `Makefile.build.inc`.


### Usage of `liburcu-bp`

  1. `#include <urcu-bp.h>`
  2. Link with `-lurcu-bp`

The BP library flavor stands for "bulletproof". It is specifically
designed to help tracing library to hook on applications without
requiring to modify these applications. `rcu_init()`,
`rcu_register_thread()` and `rcu_unregister_thread()` all become nops.
The state is dealt with by the library internally at the expense of
read-side and write-side performance.


### Initialization

Each thread that has reader critical sections (that uses
`rcu_read_lock()`/`rcu_read_unlock()` must first register to the URCU
library. This is done by calling `rcu_register_thread()`. Unregistration
must be performed before exiting the thread by using
`rcu_unregister_thread()`.


### Reading

Reader critical sections must be protected by locating them between
calls to `rcu_read_lock()` and `rcu_read_unlock()`. Inside that lock,
`rcu_dereference()` may be called to read an RCU protected pointer.


### Writing

`rcu_assign_pointer()` and `rcu_xchg_pointer()` may be called anywhere.
After, `synchronize_rcu()` must be called. When it returns, the old
values are not in usage anymore.


### Usage of `liburcu-defer`

  - Follow instructions for either `liburcu`, `liburcu-qsbr`,
    `liburcu-mb`, `liburcu-signal`, or `liburcu-bp` above.
    The `liburcu-defer` functionality is pulled into each of
    those library modules.
  - Provides `defer_rcu()` primitive to enqueue delayed callbacks. Queued
    callbacks are executed in batch periodically after a grace period.
    Do _not_ use `defer_rcu()` within a read-side critical section, because
    it may call `synchronize_rcu()` if the thread queue is full.
    This can lead to deadlock or worse.
  - Requires that `rcu_defer_barrier()` must be called in library destructor
    if a library queues callbacks and is expected to be unloaded with
    `dlclose()`.

Its API is currently experimental. It may change in future library releases.


### Usage of `urcu-call-rcu`

  - Follow instructions for either `liburcu`, `liburcu-qsbr`,
    `liburcu-mb`, `liburcu-signal`, or `liburcu-bp` above.
    The `urcu-call-rcu` functionality is pulled into each of
    those library modules.
  - Provides the `call_rcu()` primitive to enqueue delayed callbacks
    in a manner similar to `defer_rcu()`, but without ever delaying
    for a grace period.  On the other hand, `call_rcu()`'s best-case
    overhead is not quite as good as that of `defer_rcu()`.
  - Provides `call_rcu()` to allow asynchronous handling of RCU
    grace periods.  A number of additional functions are provided
    to manage the helper threads used by `call_rcu()`, but reasonable
    defaults are used if these additional functions are not invoked.
    See [`doc/rcu-api.md`](doc/rcu-api.md) in userspace-rcu documentation
    for more details.


### Being careful with signals

The `liburcu` library uses signals internally. The signal handler is
registered with the `SA_RESTART` flag. However, these signals may cause
some non-restartable system calls to fail with `errno = EINTR`. Care
should be taken to restart system calls manually if they fail with this
error. A list of non-restartable system calls may be found in
`signal(7)`. The `liburcu-mb` and `liburcu-qsbr` versions of the Userspace RCU
library do not require any signal.

Read-side critical sections are allowed in a signal handler,
except those setup with `sigaltstack(2)`, with `liburcu` and
`liburcu-mb`. Be careful, however, to disable these signals
between thread creation and calls to `rcu_register_thread()`, because a
signal handler nesting on an unregistered thread would not be
allowed to call `rcu_read_lock()`.

Read-side critical sections are _not_ allowed in a signal handler with
`liburcu-qsbr`, unless signals are disabled explicitly around each
`rcu_quiescent_state()` calls, when threads are put offline and around
calls to `synchronize_rcu()`. Even then, we do not recommend it.


### Interaction with mutexes

One must be careful to do not cause deadlocks due to interaction of
`synchronize_rcu()` and RCU read-side with mutexes. If `synchronize_rcu()`
is called with a mutex held, this mutex (or any mutex which has this
mutex in its dependency chain) should not be acquired from within a RCU
read-side critical section.

This is especially important to understand in the context of the
QSBR flavor: a registered reader thread being "online" by
default should be considered as within a RCU read-side critical
section unless explicitly put "offline". Therefore, if
`synchronize_rcu()` is called with a mutex held, this mutex, as
well as any mutex which has this mutex in its dependency chain
should only be taken when the RCU reader thread is "offline"
(this can be performed by calling `rcu_thread_offline()`).


### Interaction with `fork()`

Special care must be taken for applications performing `fork()` without
any following `exec()`. This is caused by the fact that Linux only clones
the thread calling `fork()`, and thus never replicates any of the other
parent thread into the child process. Most `liburcu` implementations
require that all registrations (as reader, `defer_rcu` and `call_rcu`
threads) should be released before a `fork()` is performed, except for the
rather common scenario where `fork()` is immediately followed by `exec()` in
the child process. The only implementation not subject to that rule is
`liburcu-bp`, which is designed to handle `fork()` by calling
`rcu_bp_before_fork`, `rcu_bp_after_fork_parent` and
`rcu_bp_after_fork_child`.

Applications that use `call_rcu()` and that `fork()` without
doing an immediate `exec()` must take special action.  The parent
must invoke `call_rcu_before_fork()` before the `fork()` and
`call_rcu_after_fork_parent()` after the `fork()`. The child
process must invoke `call_rcu_after_fork_child()`.
Even though these three APIs are suitable for passing to
`pthread_atfork()`, use of `pthread_atfork()` is **STRONGLY
DISCOURAGED** for programs calling the glibc memory allocator
(`malloc()`, `calloc()`, `free()`, ...) within `call_rcu` callbacks.
This is due to limitations in the way glibc memory allocator
handles calls to the memory allocator from concurrent threads
while the `pthread_atfork()` handlers are executing.

Combining e.g.:

  - call to `free()` from callbacks executed within `call_rcu` worker
    threads,
  - executing `call_rcu` atfork handlers within the glibc pthread
    atfork mechanism,

will sometimes trigger interesting process hangs. This usually
hangs on a memory allocator lock within glibc.


### Thread Local Storage (TLS)

Userspace RCU can fall back on `pthread_getspecific()` to emulate
TLS variables on systems where it is not available. This behavior
can be forced by specifying `--disable-compiler-tls` as configure
argument.


### Usage of `DEBUG_RCU`

`DEBUG_RCU` is used to add internal debugging self-checks to the
RCU library. This define adds a performance penalty when enabled.
Can be enabled by uncommenting the corresponding line in
`Makefile.build.inc`.


### Usage of `DEBUG_YIELD`

`DEBUG_YIELD` is used to add random delays in the code for testing
purposes.


### SMP support

By default the library is configured to use synchronization primitives
adequate for SMP systems. On uniprocessor systems, support for SMP
systems can be disabled with:

    ./configure --disable-smp-support

theoretically yielding slightly better performance.


Make targets
------------

In addition to the usual `make check` target, Userspace RCU features
`make regtest` and `make bench` targets:

  - `make check`: short tests, meant to be run when rebuilding or
    porting Userspace RCU.
  - `make regtest`: long (many hours) test, meant to be run when
    modifying Userspace RCU or porting it to a new architecture or
    operating system.
  - `make bench`: long (many hours) benchmarks.


Contacts
--------

You can contact the maintainers on the following mailing list:
`lttng-dev@lists.lttng.org`.
