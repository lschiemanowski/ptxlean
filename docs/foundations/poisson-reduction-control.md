# From tree control to shared-memory visibility

The 256-lane shared reduction tree now has a source-selection theorem for
**every read in every finite execution admitted by the fragment's explicit
source rules**. It does not assume the answer to a load, a table of preceding
stores, or the presence of a barrier edge. It derives those facts from the
instructions and their execution.

This closes the structural premises identified in the
[reduction source guide](poisson-reduction-sources.md) for the shared-tree
fragment. It is not yet a theorem for the complete emitted dot-product entry.

## The fragment and its inputs

Each of 256 threads starts with its lane number in register 14, the common
shared-memory base in register 3, and an arbitrary partial sum in register 8.
The base must leave room for 2048 bytes without address wraparound. The
barrier starts empty and every thread starts at instruction position zero.
Each lane publishes its partial sum to its own eight-byte slot. After a
barrier, the tree has eight stages with 128, 64, 32, 16, 8, 4, 2 and 1 active
lanes. Each stage reads a lane's own slot and a neighbor's slot, adds them
with the existing binary64 instruction semantics, stores into its own slot,
and ends with a barrier attended by all lanes.

The fragment uses the existing combined lane-test/branch instruction.
The emitted PTX uses a predicate-producing instruction followed by a
predicated branch. Their translation still needs a proof. The fragment also
starts **after** the global strided accumulation loop and ends **before** the
final global output store. In particular, its arbitrary input partial sums
are not presumed to be the correct dot products.

The abstract program has 68 instruction positions:

| Operation | Position | Participating lanes |
| --- | --- | --- |
| Initial store | 2 | 0 through 255 |
| Initial barrier | 3 | All lanes |
| Stage k guard, for k = 0 through 7 | 4 + 8k | All lanes |
| Own-word load | 7 + 8k | lane < 256 / 2^(k+1) |
| Neighbor-word load | 8 + 8k | Same active lanes |
| Replacement store | 10 + 8k | Same active lanes |
| Stage barrier | 11 + 8k | All lanes |

These are positions in the abstract program, not native PTX instruction
positions. Inactive lanes skip the six-instruction update and reach its
barrier.

## Why a read sees the preceding publication

There are four parts to the argument.

1. **Control limits the writers.** A bound at each program position says how
   many lanes can reach it. Arithmetic preserves that bound, the lane guard
   establishes the narrower bound, and barrier release advances all lanes
   to a position admitting them. Induction over the actual interleaving
   proves these bounds for every observed access. Finite checks establish
   the control conditions for all eight stages; they do not enumerate input
   values or execution histories.
2. **Address preparation establishes ownership.** The program preserves the
   lane number and shared base. It computes `base + 8 * lane` and preserves
   that address register through the loads and addition. Thus every store
   belongs to that lane's slot. No value or source constraints are used to
   prove this fact.
3. **An observed later read entails a real producer.** A lane active at the
   preceding publication cannot skip its store. No lane can skip that
   publication's following barrier. Reaching a later read therefore entails
   the producer's actual store, its arrival, and a completed barrier, in that
   order. This also works for a producer different from the reader.
4. **The source rules exclude the wrong publication.** For an own-slot read,
   the next write is after the read in the same thread. For a neighbor read,
   the neighbor is outside the new active range and cannot write again.
   Byte compatibility and the necessary repeated-write coherence rules then
   force each source byte to come from the actual preceding publication.

The theorem does not infer causality merely from the order of events in a
list. Same-thread instruction order and actual barrier events establish the
required causal edges.

## Reading the Lean result

The main theorem is `Control.every_read` in
[`ReductionReads.lean`](../../integration/torchlean/PoissonPTX/ReductionReads.lean).
Its premises are an actual finite execution, the entry register and barrier
conditions above, byte-compatible sources, and `OrderedSources`, the explicit
necessary coherence and causality constraints. Its conclusion identifies the
read's stage, its owner lane, an actual store at the preceding publication
site, equality of the loaded word to that store's word, and the identity of
all eight source bytes. It has no producer-occurrence, read-address,
store-coverage, barrier-edge or read-value premise.

The supporting files are:

- [`ConcurrentLimits.lean`](../../integration/torchlean/PoissonPTX/ConcurrentLimits.lean):
  reusable program-position lane bounds.
- [`ConcurrentAddressHold.lean`](../../integration/torchlean/PoissonPTX/ConcurrentAddressHold.lean):
  address facts that survive loads and arithmetic.
- [`ReductionControl.lean`](../../integration/torchlean/PoissonPTX/ReductionControl.lean):
  the concrete shared tree and active store classification.
- [`ReductionOwnership.lean`](../../integration/torchlean/PoissonPTX/ReductionOwnership.lean):
  store addresses and the derived stage-coverage contract.
- [`ReductionPublication.lean`](../../integration/torchlean/PoissonPTX/ReductionPublication.lean):
  actual publication and barrier causality.

Negative checks in `ReductionControlChecks.lean` reject a guard that admits
too many writers, a branch that skips the barrier, and an addition that
clobbers the address register. The earlier four-lane positive and obsolete
source executions remain independent concrete regressions.

## What this does not establish

This is a universal conditional visibility result, not a construction of a
complete 256-lane execution. Existence for arbitrary initial words, the
composition of the actual additions into the specified rounded numerical
tree, and full memory-safety/progress results remain separate obligations.
The local six-instruction update already has its own correctness, execution
existence and allocation bounds; this change does not silently lift those to
the whole entry.

`OrderedSources` is a necessary fragment of the PTX memory rules, not a full
PTX admission model. The model remains restricted to synchronous full-block
barriers and separate identity-addressed shared/global spaces. Native branch
translation, the input accumulation loop, output publication, host launch
composition, the complete PCG solver and hardware conformance remain open.
No GPU execution or new empirical claim is part of this result.
