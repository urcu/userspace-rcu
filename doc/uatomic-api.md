<!--
SPDX-FileCopyrightText: 2023 EfficiOS Inc.

SPDX-License-Identifier: CC-BY-4.0
-->

Userspace RCU Atomic Operations API
===================================

by Mathieu Desnoyers and Paul E. McKenney

This document describes the `<urcu/uatomic.h>` API. Those are the atomic
operations provided by the Userspace RCU library. The general rule
regarding memory barriers is that only `uatomic_xchg()`,
`uatomic_cmpxchg()`, `uatomic_add_return()`, and `uatomic_sub_return()` imply
full memory barriers before and after the atomic operation. Other
primitives don't guarantee any memory barrier.

Only atomic operations performed on integers (`int` and `long`, signed
and unsigned) are supported on all architectures. Some architectures
also support 1-byte, 2-byte and 8-byte atomic operations. Those respectively
have `UATOMIC_HAS_ATOMIC_BYTE`, `UATOMIC_HAS_ATOMIC_SHORT` and
`UATOMIC_HAS_ATOMIC_LLONG` defined when `uatomic.h` is included. Trying to
perform an atomic operation on a type size not supported by the architecture
will result in a static assert at compile time.

In the description below, `type` is a type that can be atomically
written to by the architecture. It needs to be at most word-sized, and
its alignment needs to greater or equal to its size.


API
---

```c
void uatomic_set(type *addr, type v);
```

Atomically write `v` into `addr`. By "atomically", we mean that no
concurrent operation that reads from addr will see partial
effects of `uatomic_set()`.


```c
type uatomic_read(type *addr);
```

Atomically read `v` from `addr`. By "atomically", we mean that
`uatomic_read()` cannot see a partial effect of any concurrent
uatomic update.


```c
type uatomic_cmpxchg(type *addr, type old, type new);
```

An atomic read-modify-write operation that performs this
sequence of operations atomically: check if `addr` contains `old`.
If true, then replace the content of `addr` by `new`. Return the
value previously contained by `addr`. This function implies a full
memory barrier before and after the atomic operation on success.
On failure, no memory order is guaranteed.


```c
type uatomic_xchg(type *addr, type new);
```

An atomic read-modify-write operation that performs this sequence
of operations atomically: replace the content of `addr` by `new`,
and return the value previously contained by `addr`. This
function implies a full memory barrier before and after the atomic
operation.


```c
type uatomic_add_return(type *addr, type v);
type uatomic_sub_return(type *addr, type v);
```

An atomic read-modify-write operation that performs this
sequence of operations atomically: increment/decrement the
content of `addr` by `v`, and return the resulting value. This
function implies a full memory barrier before and after the atomic
operation.


```c
void uatomic_and(type *addr, type mask);
void uatomic_or(type *addr, type mask);
```

Atomically write the result of bitwise "and"/"or" between the
content of `addr` and `mask` into `addr`.

These operations do not necessarily imply memory barriers.
If memory barriers are needed, they may be provided by explicitly using
`cmm_smp_mb__before_uatomic_and()`, `cmm_smp_mb__after_uatomic_and()`,
`cmm_smp_mb__before_uatomic_or()`, and `cmm_smp_mb__after_uatomic_or()`.
These explicit barriers are no-ops on architectures in which the underlying
atomic instructions implicitly supply the needed memory barriers.


```c
void uatomic_add(type *addr, type v);
void uatomic_sub(type *addr, type v);
```

Atomically increment/decrement the content of `addr` by `v`.
These operations do not necessarily imply memory barriers.
If memory barriers are needed, they may be provided by
explicitly using `cmm_smp_mb__before_uatomic_add()`,
`cmm_smp_mb__after_uatomic_add()`, `cmm_smp_mb__before_uatomic_sub()`, and
`cmm_smp_mb__after_uatomic_sub()`. These explicit barriers are
no-ops on architectures in which the underlying atomic
instructions implicitly supply the needed memory barriers.


```c
void uatomic_inc(type *addr);
void uatomic_dec(type *addr);
```

Atomically increment/decrement the content of `addr` by 1.
These operations do not necessarily imply memory barriers.
If memory barriers are needed, they may be provided by
explicitly using `cmm_smp_mb__before_uatomic_inc()`,
`cmm_smp_mb__after_uatomic_inc()`, `cmm_smp_mb__before_uatomic_dec()`,
and `cmm_smp_mb__after_uatomic_dec()`. These explicit barriers are
no-ops on architectures in which the underlying atomic
instructions implicitly supply the needed memory barriers.
