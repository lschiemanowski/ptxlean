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

The standalone input-loop theorem uses a scalar global-byte snapshot. The
complete concurrent entry now derives that input snapshot from actual memory
sources. Joining the resulting partial sums to the shared-tree theorem and
proving the final shared load and output value remain separate obligations.
Text bindings are frontend checks; neither Lean checking nor successful text
comparison establishes compiler or GPU conformance.

[DotInputComplete.lean](../../integration/torchlean/PoissonPTX/DotInputComplete.lean)
proves `input_correct` and `input_exists` for the actual setup and loop.
For 257 elements, lane zero reads indices 0 and 256; lane one reads only
index 1. With one element, lanes 1 through 255 perform no loads and retain
positive zero. The proof does not reassociate any floating-point sums.
`DotInputChecks` covers these boundaries and shows why removing the unsigned
size bound would permit wraparound. `hardware/check_poisson_dot_input.py`
compares every input-loop instruction, resolves its labels and checks field
bounds and the single-block launch shape.

## Complete concurrent entry and input sources

The complete dot entry has one concurrent fetched program with 104 instruction
positions: input setup and accumulation, the shared tree, and the output tail.
Its predicates are thread-local values and its barriers use actual arrival and
completion events. A returned thread has executed a return instruction; that
is not inferred from a convenient instruction counter. A fast thread may
publish its partial sum while another is still reading input vectors. There
is no additional barrier between those phases.

For every returned thread, the proof recovers its actual input execution from
the interleaving. Other threads and later instructions leave this recorded
input execution unchanged. Every retained read is connected to the original
whole-kernel memory history. The unsigned loop guard and address instructions
prove that each read belongs to one of the input arrays. Every global store in
the complete entry is proved to use the designated output address. When that
word is disjoint from the inputs, byte-source compatibility forces every input
read to recover its initialized bytes. Thus the lane's rounded partial sum
follows from actual execution and memory admission, without a supplied read
value, partial-sum equation, local execution or phase boundary.

For example, lane zero can finish a short input traversal and write its shared
slot while lane one is still loading an input. `NativeFlow` allows this
schedule. `prefix_complete` reconstructs lane one's real traversal even though
other threads have progressed farther. It proves completion because a thread
cannot return inside the input prefix or jump back into it from the tail.

`input_observations` proves which array element each actual read addresses.
`stores_output` reconstructs the output address from registers prepared by the
epilogue. `admitted_input` combines these facts with per-byte source
compatibility; shared writes cannot supply global input bytes, and the one
global output field is physically separate. `completed_input_correct` then
uses the already proved rounded fold, preserving its order and NaN behavior.
These are universal statements about admitted runs, not tests of a few words.

`hardware/check_poisson_dot_entry.py` compares all 104 instructions with the
Lean renderer, resolving every label to its absolute position. Its layout
checks enforce the single 256-thread block, 2048 shared bytes, aligned array
fields, bounded count and disjoint output word. This is source binding, not a
claim that NVIDIA hardware implements the modeled instructions.

## From the input accumulator to shared publication

The first shared publication is connected to that same thread's admitted
input traversal. A stronger projection tracks the recovered registers until
the actual store: only the two temporary address registers may change. The
shared base, lane number and accumulator therefore come from the executed
setup and input calculation. The two address instructions produce the lane's
own eight-byte slot. With a lane number below 256 and an aligned, nonwrapping
2048-byte shared allocation, the store is within bounds. Its decoded word is
that lane's ordered rounded partial sum; neither the word nor a shared-memory
snapshot is supplied as a premise.

Suppose lane seven finishes its input loop. The proof retains that exact
prefix state while the thread computes its shared address in the two temporary
registers. Other threads may execute throughout. At instruction 22, the actual
store operand is still the saved accumulator, and its address is the shared
base plus 7 × 8 bytes. This avoids substituting an unrelated local execution
that happens to have the right numerical answer.

`NativeFlow.prefix_step_exact` and `prefix_track` keep this connection explicit.
`DotPublicationRegisters` recovers the base, lane and accumulator from the same
source-admitted trace. `DotPublicationAddress` checks the two address operations;
`DotPublicationValue.publication_contents` combines the actual store address and
decoded word. `DotPublicationSafety` converts the modular address into the
nonwrapping lane slot and proves its allocation bound.

## Returns and actual barrier completions

Every returned thread has crossed all nine tree barriers, including a lane
taking the conditional return after the final barrier. Each crossing entails
an actual completion event with earlier arrivals from every thread at the
same resource, instruction site and barrier round. This follows from fetched
branch targets, return placement and the barrier state transitions. These
facts provide synchronization evidence for later reads; they do not by
themselves identify those reads' byte sources or numerical values.

`NativeFlowHistory` reuses the proved barrier-state history rules, including
all participants' arrival records. `NativeFlowBarrier` shows that a protected
barrier instruction cannot be crossed by an ordinary step or branch.
`DotBarriers` checks all nine sites and their incoming branch targets. Finally,
`DotReturns.returned_barriers` connects this to the real halt flag: it covers
both the conditional nonzero-lane return and lane zero's final return.

Suffix instruction order supplies same-thread causal edges even though the
input prefix loops. Cross-thread edges use actual stores, arrivals, completions
and reads. The shared-slot ownership and shrinking lane ranges exclude competing
writes before applying byte-source admission.

## The native tree and final output

The complete native dot entry derives the shared tree's read sources and
numerical values from its own execution. The input loop may revisit instructions,
but each shared-memory instruction occurs at most once per lane. Setup fixes
the shared base and lane number. Actual comparisons and branches restrict each
successive stage to half as many lanes, and actual address instructions keep
each writer in its own eight-byte slot. A later read has an earlier publication
connected through the same barrier's arrival and completion events. Lane
ownership and instruction order exclude stale or competing publications.
Consequently each read obtains the required preceding word, and each actual
rounded addition produces the next tree value. The last shared read obtains
lane zero's final publication; the output-address instructions preserve that
word until the global store. The resulting decoded output is the prescribed
binary64 reduction of the actual input-loop partial sums. Neither input sums,
shared snapshots, desired read values nor phase boundaries are assumed.

For example, at the first stage lane seven reads its own publication and lane
135's publication. The proof first locates both actual reads and their address
instructions. Lane 135 cannot write again after this stage because the active
range has shrunk to 128 lanes. Lane seven's next write follows its read in that
same thread. Their preceding stores and the completed barrier therefore exclude
both initialization and a different in-place update as sources. The same argument
repeats with strides 64, 32, and so on, down to one.

`DotTreeSources.tree_read_source` contains that source argument for every stage.
`DotTreeCorrect.publication_value` then follows the actual load/add/store
instructions and their explicit rounding order. Its initial case uses the
already-derived input-loop accumulator. `DotFinalRead.final_read_source` handles
the last barrier and lane-zero word, and `DotOutputValue.output_value` reaches
the actual global store. Together with `DotStores.stores_output`, this identifies
both the output word's address and its decoded value.

## A complete native execution witness

A complete native dot execution can be constructed from valid launch data.
Each lane executes its input loop from the common initialized global bytes.
The lanes then execute their initial shared stores, all nine real barrier
rounds, the actual comparison and branch instructions, and the reduction
updates. Nonzero lanes return after the final barrier; lane zero reads the
last shared publication, writes the global output and returns. The chosen
schedule is finite and may run lane bodies in sequence. It inserts no extra
barrier and does not replace shared reads with a local memory snapshot.

The construction retains every actual memory and barrier event. Global input
reads name initialization. Each shared read names the appropriate actual store;
its barrier path, lane ownership and instruction order exclude competing writes.
Byte compatibility and the fragment's ordered-source constraints hold for that
same combined history. The execution contains a real output store, and the
universal numerical theorem proves its decoded word equals the prescribed
binary64 reduction of the computed input-loop partial sums. This establishes
existence as well as conditional output correctness for the native dot entry.
It does not establish progress for every GPU schedule, full PTX memory admission,
or hardware conformance. Remaining PCG kernels and host launch composition are
separate obligations.

For an input count of 300, lane zero consumes positions 0 and 256; lane 43
consumes 43 and 299; lane 44 consumes just 44. The witness first runs each
lane's own input loop, retaining its real read records and rounded accumulator.
It then schedules the initial stores and actual barrier, followed by the eight
shrinking reduction stages and their barriers. This is one legal finite
schedule, not a constraint on the universal correctness theorem's interleavings.

`DotComplete.complete` states the combined result. `DotCompleteCandidate`
constructs the instruction run; `DotWitnessAdmission` derives compatible byte
sources for that same history. `DotOutputExists` prevents a vacuous result by
recovering the actual lane-zero output store from its completed execution.
The numerical result then uses `DotOutputValue.output_value`, independently of
the particular schedule used by the witness.

## Remaining boundaries

The complete program and its absolute branch targets are compared with emitted
PTX, including the conditional return, final shared load, output address
arithmetic and global store. Output-address ownership is proved independently
of the stored numerical value. The native numerical theorem now connects the
same input execution, shared tree, final shared read and actual output store.
A complete admitted native-entry execution witness is also constructed. The
full PCG launch sequence remains open.

`OrderedSources` remains a necessary fragment of the PTX memory rules. The
model uses synchronous full-block barriers, identity addresses, separate
shared/global spaces and no concurrent external writer. The standalone and native-entry
existence results construct finite schedules; they do not guarantee progress
under arbitrary scheduling. No new GPU run is part of this checkpoint.

The native dot-output theorem applies to every recorded global store in an
admitted execution, with 256 correctly numbered lanes, common initialized input
bytes, bounded input count, valid arrays, disjoint output storage and nonwrapping
addresses. It preserves the freedom of exceptional binary64 encodings by stating
decoded-value equality. A separate complete native-entry witness establishes
that the source-admitted execution and its output store exist. The remaining
PCG kernels and host launch composition are unfinished. Byte compatibility and ordered sources are explicit necessary
memory constraints, not a claim of full PTX admission or hardware conformance.
