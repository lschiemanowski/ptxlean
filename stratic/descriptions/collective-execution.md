# Collective execution

A collective instruction coordinates several threads. A CTA (cooperative thread
array) is one launched thread block. Within it, threads are arranged in smaller
execution groups called warps. A block barrier is a meeting point: each thread
arrives, waits for the required participants, and then continues. A waiting
thread cannot issue an instruction after the barrier.

The first foundation is an unconditionally reached `bar.sync 0` with every
thread of one CTA participating and no thread exiting before the barrier.
There is no explicit thread count. Threads execute the same instruction site;
this is the collective-control promise called aligned. It is separate from
alignment of a memory address. The model records individual arrivals and proves
that requiring every thread is equivalent to requiring every complete warp in
this restricted setting.

Each use has its own generation, a number that advances on completion. Arrivals
from an earlier use cannot release a later one. The barrier belongs to its CTA;
sharing the numeric resource name with another CTA does not make it the same
barrier. Counting a waiting thread again must have no effect. Runnable means
allowed to execute, not guaranteed immediate execution by a GPU scheduler.

Control coordination and memory visibility need separate proofs. A completed
barrier orders participating threads' preceding ordinary accesses before their
following accesses. The memory account must derive those connections from actual
arrival and completion events; it must not assume that a read already saw the
required value. Splitting arrival from completion avoids inventing a cycle
between collective operations. Successive generations remain distinct.

A shared-memory example must use actual shared-state-space loads and stores,
valid addresses inside storage owned by that CTA, and explicit instruction
ordering qualifiers. A simulator with immediate shared-memory updates can give
an execution witness; it does not enumerate every PTX memory behavior. Universal
correctness therefore uses separately justified memory constraints. Initial
values, read-source choices, arithmetic, safety and finite execution existence
remain visible in the proof.

This first slice targets PTX 9.4 and GPUs at least `sm_70` for its modern memory
rules. The barrier instruction itself exists on older targets. Explicit counts,
dynamic resource selection, early exits, divergent participation, other barrier
forms, and asynchronous completion require further semantics. Unsupported forms
are not automatically illegal PTX, and waiting is not undefined behavior.
