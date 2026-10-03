# Correctness and existence of the shared reduction tree

The 256-lane shared reduction tree now has three complementary results:

- **Correctness:** every completed execution admitted by the stated source
  rules contains a final store computing the specified eight-round binary64
  reduction of its original lane partial sums.
- **Existence:** valid input storage and arbitrary initial words give a
  constructed finite execution, completed barriers and admitted byte sources.
- **Memory safety:** every recorded access belongs to the original aligned
  2048-byte shared allocation, independently of source admission.

These are results for the shared-tree fragment. The complete emitted dot-product
entry still needs its native control translation, global input loop and output
epilogue connected. No exact-real summation or bitwise equality to a sequential
CPU reduction is asserted.

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

The source-selection theorem is `Control.every_read` in
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

## From read sources to the numerical answer

[`ReductionCorrect.lean`](../../integration/torchlean/PoissonPTX/ReductionCorrect.lean)
proves `Numeric.publication_value` for every publication and
`Numeric.completed_result` for the actual final store. At round zero, the store
contains the lane's original accumulator. At each later round, source selection
recovers the preceding publications. A reusable register analysis in
`ConcurrentValues.lean` follows the actual loads and floating-point addition
and identifies the actual store-source register. Induction over the eight
rounds gives `Binary64.reduce256`, the existing numerical specification.

The addition order is exactly the tree order. Each addition rounds separately.
The result equates decoded binary64 values, including their exceptional
classifications, while preserving the primitive instruction contract's freedom
in NaN payload bits. The universal theorem does not restrict input words to
finite numbers or impose the constructor's canonical choice of output bits.

## Constructing a complete admitted execution

[`ReductionComplete.lean`](../../integration/torchlean/PoissonPTX/ReductionComplete.lean)
proves `Witness256.exists_correct`. Its inputs describe registers, allocation,
alignment, entry positions and an empty barrier with no pending site. It takes
no execution, read result, expected publication table or numerical answer as a
premise.

The construction runs each phase's lane bodies sequentially, then completes
the barrier with all 256 participants. Sequential scheduling is a convenient
existence witness; the correctness theorem still covers arbitrary admitted
interleavings. Generic local-block and lane-family lemmas avoid expanding one
enormous concrete interpreter computation.

The chosen loads use exact preceding word encodings. Each arithmetic operation
chooses its permitted canonical encoding. The constructor proves these facts
about its actual event records. Fetched control then provides the actual
producer occurrences and barrier edges. Those facts construct compatible byte
sources and a coherence witness satisfying `OrderedSources`. Thus successful
instruction execution and source admission hold for the same constructed run.
No value needed for a future load is installed in a thread's shared memory as
an unexplained assumption.

[`ReductionSafety.lean`](../../integration/torchlean/PoissonPTX/ReductionSafety.lean)
proves the separate universal access bound. The construction also proves each
instruction's required access validity and preserves the input layout across
all rounds.

`ReductionCompleteChecks.lean` instantiates existence with arbitrary initial
bit patterns. Its cancellation example constructs a complete admitted run with
result two, whereas the existing sequential-fold example gives one. This
exercises the connection to the specified numerical ordering without evaluating
an entire 256-thread trace inside the proof checker.

## Remaining boundaries

The full emitted entry still needs native predicate/branch translation, the
strided global input accumulation loop and the final global output store. The
fragment begins with supplied partial sums, so it does not yet prove that those
sums represent the original input vectors.

`OrderedSources` remains a necessary fragment of the PTX memory rules, not a
full PTX admission model. The model uses synchronous full-block barriers and
separate identity-addressed shared/global spaces. The existence theorem proves
that a finite completed schedule exists; it does not guarantee progress under
arbitrary external scheduling. Host launch composition, the complete PCG solver
and hardware conformance remain separate. No new GPU execution or empirical
claim is part of this result.
