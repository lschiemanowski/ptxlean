# Three reads before one write, including aliases

[Ptx/AffineMemory.lean](../../Ptx/AffineMemory.lean) proves the memory part of a
single-thread pattern: read three inputs, then write one output. The inputs and
output can name any valid whole word of the same initialized arena. They can all
name the same word. This module has no floating-point imports and does not decide
what arithmetic result should be stored.

## Why the order matters

Suppose an arena contains one word, `0x3f800000`. All three input arguments and the
output argument name it. The proposed final store writes `0x40000000`. Each read
must still return `0x3f800000`: the write occurs after the reads. The
`all_alias_example` theorem constructs a valid graph for exactly this situation.
These are merely two different 32-bit patterns here; interpreting them as real
numbers belongs to the numerical layer.

The graph contains one initialization event for each arena word, followed by
four program memory events. There are three loads at instruction positions 0,
1 and 2, and one store at position 5. Positions 3 and 4 leave room for arithmetic;
the graph does not pretend to execute those instructions. Initialization events
have no issuing thread. All four program events belong to thread zero.

It is important to create initialization events per **location**, rather than
per argument. Otherwise two aliased arguments could acquire separate initial
writes to the same word. Here several reads can select the same initialization.

## A universal result and an existence result

`valid_reads_initial` quantifies over proposed read words, the stored word,
every read-source function and every write-order relation. Its only semantic
premise is the resulting graph's `Graph.Valid` predicate. It concludes that all
three reads equal the initial values at their respective addresses.

The proof does not assume that those sources are initial. Source compatibility
first says that a source is a write at the read's address. Besides initialization,
the sole possible write is the final store. If a read selected that store,
program order and the matching address would place it causally after the read.
The existing `no_future` clause rules this out. The remaining source must be the
unique initialization at that address, whose value is known.

`witness_valid` proves that the desired observations are possible under the graph
rules, for arbitrary initial memory and any proposed stored word. Its source
function selects the appropriate initial event for each read. Its write order
contains exactly the output location's initialization followed by the store.
The proof checks source compatibility, write order, both causality requirements,
and the absence of forbidden ordering cycles. It uses increasing finite event
indices as a proof device, without changing the definition of memory validity.

| Obligation | Reason in this witness |
| --- | --- |
| Compatible read sources | The unique initialization has exactly the read's address and value. |
| Coherence, or order of writes at one location | Only the output word has two writes; its initialization precedes the store. |
| No cyclic base order | Single-thread program positions strictly increase. |
| Writes ordered by causality respect coherence | No initialization has outgoing program order; the only program write has no later program write. |
| No read from a causally later write | Every selected source is initialization, never the final store. |
| No stale read after a causally earlier write | The sole program write follows every load, so there is no such write-to-read path. |
| Sequential consistency at each location | Relevant program-order and communication edges strictly increase event indices. |

Fence and read-modify-write instructions have no instances in this event shape.
Every read takes one complete word from one source, retaining the existing
whole-word treatment of single-copy atomicity.

`witness_grounding_rank` additionally proves that every program-order or
read-source edge in this particular witness increases the event index.
`witness_grounding_acyclic` excludes their cycles. Neither theorem adds such a
condition to general PTX validity; the PTX no-thin-air rule is not equivalent to
a blanket ban on all program-order/read-source cycles.

## Checked addresses and the execution boundary

The graph's core takes word locations as finite indices. `wordIndex` converts a
byte address satisfying `Scalar.ValidAddress` into a location, and
`wordIndex_bytes` proves that multiplying the location by four recovers the
original byte offset. `witnessAt_valid` exposes the existence result directly
for three checked input byte addresses and one checked output byte address.
There is no distinctness premise.

This module proves an abstract event-shape theorem. The separate
[affine execution bridge](../../integration/torchlean/PtxBinary32/Affine.lean)
now supplies `trace_memory_witness`: these four program labels equal **all**
memory effects projected from the actual fetched trace, retaining addresses,
values and dispatch positions. Initial events come separately from the supplied
initial arena. `run_memory_witness` specializes the arbitrary stored word to the
actual final memory output of every admitted terminal run. The local `run_iff`
and `run_grounded` proofs connect that word to the initial loads, multiplication
and addition and prove that actual register dependencies go forward. The graph
theorem alone still supplies neither arithmetic correspondence nor a general
dependency-sensitive no-thin-air model. The complete connection is explained in
the [mixed affine study guide](mixed-affine.md).

## Source interpretation and limits

The normative source is the [pinned PTX 9.4 manual](../../references/nvidia/ptx-isa-9.4/README.md),
SHA-256 `0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The key clauses are [program order](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#program-order),
[causality order](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#causality-order),
[the causality axiom](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#causality-axiom),
[initialization](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#initialization),
and [SC per location](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#sc-per-loc-axiom).
The [source ledger](source-ledger.md) explains the inherited graph relations and
normalization of four initial bytes into one word event.

The interpretation is restricted to aligned scalar `.u32` global loads/stores,
explicit `.relaxed.gpu` ordering, one GPU, ordinary generic-proxy access, and an
`sm_70`-or-later target. The represented arena is isolated from other threads,
host actions and asynchronous operations. Full-word aliases are supported;
partial overlaps, mixed widths and different virtual addresses naming the same
physical storage are not. The distinct finite locations still denote disjoint
four-byte footprints. Resolved arena offsets are not a proof of runtime pointer
translation, permissions, launch behavior or hardware conformance.

The Lean build and [dependency audit](affine-memory-audit.txt) establish the
formal claims, with only Lean's standard axioms. Matching those definitions to
the documented PTX slice is a separately reviewed source interpretation.
