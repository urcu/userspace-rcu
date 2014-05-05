Userspace RCU Concurrent Data Structures (CDS) API
==================================================

by Mathieu Desnoyers and Paul E. McKenney

This document describes briefly the data structures contained with the
userspace RCU library.


Data structure files
--------------------

### `urcu/list.h`

Doubly-linked list, which requires mutual exclusion on
updates and reads.


### `urcu/rculist.h`

Doubly-linked list, which requires mutual exclusion on
updates, allows RCU read traversals.


### `urcu/hlist.h`

Doubly-linked list, with single pointer list head. Requires
mutual exclusion on updates and reads. Useful for implementing hash tables.
Downside over `list.h`: lookup of tail in O(n).


### `urcu/rcuhlist.h`

Doubly-linked list, with single pointer list head.
Requires mutual exclusion on updates, allows RCU read traversals. Useful
for implementing hash tables. Downside over rculist.h: lookup of tail in O(n).


### `urcu/wfstack.h`

Stack with wait-free push and wait-free pop_all. Both
blocking and non-blocking pop and traversal operations are provided. This
stack does _not_ specifically rely on RCU. Various synchronization techniques
can be used to deal with pop ABA. Those are detailed in the API.


### `urcu/wfcqueue.h`

Concurrent queue with wait-free enqueue. Both blocking and
non-blocking dequeue, splice (move all elements from one queue
to another), and traversal operations are provided.
    
This queue does _not_ specifically rely on RCU. Mutual exclusion
is used to protect dequeue, splice (from source queue) and
traversal (see API for details).

  - Note: deprecates `urcu/wfqueue.h`.


### `urcu/lfstack.h`

Stack with lock-free push, lock-free pop, wait-free pop_all,
wait-free traversal. Various synchronization techniques can be
used to deal with pop ABA. Those are detailed in the API.
This stack does _not_ specifically rely on RCU.

  - Note: deprecates `urcu/rculfstack.h`.


### `urcu/rculfqueue.h`

RCU queue with lock-free enqueue, lock-free dequeue.
This queue relies on RCU for existence guarantees.


### `urcu/rculfhash.h`

Lock-Free Resizable RCU Hash Table. RCU used to provide
existance guarantees. Provides scalable updates, and scalable
RCU read-side lookups and traversals. Unique and duplicate keys
are supported. Provides "uniquify add" and "replace add"
operations, along with associated read-side traversal uniqueness
guarantees. Automatic hash table resize based on number of
elements is supported. See the API for more details.
