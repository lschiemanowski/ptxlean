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
in-place output address and unsigned guard. The parallel proof derives old inputs from the same actual interleaved history
and publishes the separately rounded update. The full PCG loop remains separate.

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
Actual launch-derived ownership and instruction order discharge these conditions for the direction update.

Consider a single thread which loads p and later stores that same loaded value
back. If initial p is zero, byte compatibility alone can still propose that the
load reads the value one from the later store. The proposed store then repeats
one, apparently justifying the load. This is circular: no executed earlier
operation supplied the one. `GlobalThreadSourceChecks.compatibility_alone`
checks this counterexample; `circular_rejected` proves that the explicit future-
store exclusion rejects it.

`AffineUpdateSources.Arena.read_value` now proves those facts for the actual
entry. `ObservedParallelNative.before_of_pc` embeds its same event history in
the native machine and derives event order from actual instruction counters.
`GlobalThreadSources.before_own_writes_initial` then excludes every store source.

## Parallel replay, publication and existence

The parallel direction update derives all input reads from its actual
interleaved history. Launch registers select disjoint eight-byte p slots.
The coefficient and z array are read-only. The old p read occurs at instruction
13 and its owning thread's store at instruction 23; no other thread can write
that word. Actual same-thread instruction order and the explicit no-future
source constraint force the read to obtain initialization bytes. Neither old
input values nor desired output equations are assumptions.

Scalar replay preserves only reads that remain to execute. It permits the
in-place write after the last read instead of requiring input/output separation.
Every completed admitted active-thread interleaving publishes z + beta*p with
separate binary64 multiply and add roundings. Bytes outside the p array remain
unchanged, including the coefficient, other vectors and padding. The result
states decoded equality and allows exceptional encoding freedom.

A finite execution with compatible initial-byte sources and the no-future
constraint exists for every valid array layout and arbitrary input words.
Its numerical result follows from the same universal publication theorem.
The joint launch contains active coordinates; padding returns are proved
separately at the per-thread level. This does not establish full PTX admission,
CUDA visibility, progress for every schedule, hardware conformance or complete
PCG launch composition.

For example, two lanes may interleave their coefficient and vector loads in any
order. They each read their own old p, and either may store first. Once lane zero
has consumed its p, its store need not preserve that old value for lane zero:
there is no future read of it. Lane one's future read uses a disjoint slot.
`ObservedTemporalReplay.replay_temporal` expresses this distinction and recovers
actual scalar instruction execution without assuming full input/output separation.

`AffineUpdateParallel.Arena.parallel_value` proves the published vector formula.
`publication_outside` preserves every byte outside p, even for incomplete runs.
`AffineUpdateExists.Arena.parallel_exists` constructs a finite run and proves
its sources and numerical result together. No input finiteness condition is
needed for these instruction-level decoded-value statements.

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

The other state updates, scalar decision kernels and the host PCG loop still need
their instruction-level composition. The accepted solver target remains a fresh
residual bound for the same discrete equations, rather than CPU-iterate bitwise
identity or a convergence claim for every input.
