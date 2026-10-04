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
entry still needs its input loop, tree and output epilogue joined under
one concurrent execution and source history. Native guard translation and the
scalar input-loop result are described below. No exact-real summation or bitwise equality to a sequential
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
predicated branch. The separate-instruction extension below now proves their translation. The fragment also
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

## Separate native comparisons and branches

The shared-tree guard now also has a proof for two separately scheduled
instructions. The comparison reads the actual unsigned lane register and writes
a private predicate; the branch subsequently reads that predicate. Other
threads may run between them. The proof derives the predicate value and shows
that a waiting barrier cannot advance a thread still between comparison and
branch. Erasing comparisons produces an actual execution of the proved tree
with the same data and barrier events. Conversely, its complete admitted
execution expands to a run with the separate instructions, so correctness,
existence and memory safety all carry across.

The counter representation records an instruction slot and whether its guard
is between comparison and branch. A checked position map connects these to the
76 actual instruction positions, including branch targets and barrier release.
Event counters retain stable slot identities; they are not native instruction
indices or machine byte addresses. A frontend resolves emitted labels and
compares the entire tree to the rendered Lean program, rejecting altered
predicates, targets, stores, barriers and branches entering from outside.

The proof lives in [ReductionNative.lean](../../integration/torchlean/PoissonPTX/ReductionNative.lean).
`NativeGuardInvariant.project` permits arbitrary interleavings; `NativeGuardExists.lift`
constructs one expanded schedule. `ReductionNativeCode` checks the instruction
positions, and `hardware/check_poisson_reduction_tree.py` compares the emitted
slice with Lean's renderer. The input accumulator remains an explicit input to
this tree theorem.

## Strided input accumulation

The complete 20-instruction setup and input loop now has a per-lane fetched
execution proof. Setup derives the lane, arena and shared-base registers from
launch context and initializes the accumulator to positive zero. The loop
compares the actual unsigned cursor with the array length, reads both input
words, performs separate rounded multiplication and addition, and advances
by 256. Every completed run equals the ordered fold over lane, lane+256 and
subsequent in-range indices; no loaded values or partial-sum answers are assumed.
Aligned contiguous fields in a nonwrapping arena supply all access bounds.
The supported length below 2^30 prevents unsigned index wraparound and gives
a decreasing count of remaining indices, constructing a finite execution for
arbitrary input words. Short and uneven arrays naturally leave some lanes
empty or with fewer iterations.

This input-loop theorem uses a scalar global-byte snapshot. The full parallel
entry still must derive that snapshot from admitted memory sources, join its
computed partial sums to the tree under interleaving, and prove the final
shared load and global output store. The native-tree and input-loop results
are individually complete components, not a completed dot-product or PCG
correspondence. Their text bindings are frontend checks; neither Lean checking
nor successful text comparison establishes compiler or GPU conformance.

[DotInputComplete.lean](../../integration/torchlean/PoissonPTX/DotInputComplete.lean)
proves `input_correct` and `input_exists` for the actual setup and loop.
For 257 elements, lane zero reads indices 0 and 256; lane one reads only
index 1. With one element, lanes 1 through 255 perform no loads and retain
positive zero. The proof does not reassociate any floating-point sums.
`DotInputChecks` covers these boundaries and shows why removing the unsigned
size bound would permit wraparound. `hardware/check_poisson_dot_input.py`
compares every input-loop instruction, resolves its labels and checks field
bounds and the single-block launch shape.

## Remaining boundaries

The full emitted entry still needs the strided input loop, shared tree and
final global output store composed under one admitted concurrent execution. The
fragment begins with supplied partial sums, so it does not yet prove that those
sums represent the original input vectors.

`OrderedSources` remains a necessary fragment of the PTX memory rules, not a
full PTX admission model. The model uses synchronous full-block barriers and
separate identity-addressed shared/global spaces. The existence theorem proves
that a finite completed schedule exists; it does not guarantee progress under
arbitrary external scheduling. Host launch composition, the complete PCG solver
and hardware conformance remain separate. No new GPU execution or empirical
claim is part of this result.
