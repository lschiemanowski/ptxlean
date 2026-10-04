# PCG vector updates

PCG is the preconditioned conjugate-gradient algorithm used by the FEM solver.
Its search direction p tells the next iteration where to move. After updating
the residual and its preconditioned version z, it computes

    p[i] = z[i] + beta * p[i]

Beta is one scalar shared by the whole vector. Each thread owns one coordinate.
The old p is an input and the new p occupies the same storage, so this is an
in-place update.

## Instruction and numerical meaning

The search-direction update has a complete per-thread fetched proof. Each
active thread executes the real launch-parameter and index setup, loads scalar
β and its old p and z words, computes the separately rounded product β · p,
adds z, stores the result and returns. Every other byte remains unchanged.
Padding threads return without memory accesses. Valid allocations give finite
execution witnesses for both paths. The 25-instruction Lean program is compared
with the emitted update_p entry, including the product register, scalar address,
in-place output address and unsigned guard. This establishes the per-thread
instruction result, not yet its concurrent in-place source admission or the
full PCG loop.

`AffineUpdateCorrect.correct` covers the instruction body and permits arbitrary
binary64 values. It states decoded equality, preserving permitted exceptional
encodings. `VectorEntry.completed_body` recovers the body from the actual fetched
prologue and return. `AffineUpdateEntry.entry_correct` joins them.

The theorem does not rewrite multiplication and addition as exact real-number
operations. For example, even if a real-number identity simplifies z + beta*p,
that identity cannot remove either rounding step in this implementation.

## Why the in-place read needs care

In-place updates need a source rule beyond byte compatibility. For synchronous
same-thread accesses using ordinary addresses and the generic memory proxy,
PTX causality forbids a read from taking bytes from a later overlapping store.
The restricted rule is explicit: it applies to actual same-thread occurrence
order at the same word address. If ownership excludes other writers, it forces
the old value to come from initialization. It does not order unrelated threads
or cover aliases, asynchronous accesses or the full PTX memory model. A
kernel-checked counterexample shows that byte compatibility alone accepts a
circular read justified by its own later write; the new rule rejects it.
Concurrent direction-update ownership and source proofs remain to be supplied.

Consider a single thread which loads p and later stores that same loaded value
back. If initial p is zero, byte compatibility alone can still propose that the
load reads the value one from the later store. The proposed store then repeats
one, apparently justifying the load. This is circular: no executed earlier
operation supplied the one. `GlobalThreadSourceChecks.compatibility_alone`
checks this counterexample; `circular_rejected` proves that the explicit future-
store exclusion rejects it.

`GlobalThreadSources.before_own_writes_initial` is the reusable next step. Once
a kernel proves that other lanes cannot write its word and that its own store
comes later, the read must obtain the initial bytes. Those ownership and actual
instruction-order facts are still required for the complete parallel update.

## Source fidelity

The source check used the pinned PTX 9.4 HTML digest
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The interpretation uses NVIDIA's [program order](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#program-order),
[causality order](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#causality-order)
and [causality axiom](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#causality-axiom).
For same-thread synchronous accesses, instruction order supplies program order;
using the generic proxy at the same identity address preserves that relation
into causality. The causality axiom then excludes a later overlapping store as
a source. This manual interpretation is distinct from Lean proof checking.

The new source predicate records only that necessary restriction. It is not a
complete memory-model admission checker or a GPU execution guarantee.

## Remaining work

Connect actual parallel direction-update histories to the source predicate,
derive ownership and old-input reads, then publish the resulting vector. The
other state updates, scalar decision kernels and the host PCG loop still need
their instruction-level composition. The accepted solver target remains a fresh
residual bound for the same discrete equations, rather than CPU-iterate bitwise
identity or a convergence claim for every input.
