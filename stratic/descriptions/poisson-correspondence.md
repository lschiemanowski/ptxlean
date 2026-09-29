# Poisson correspondence

A correspondence proof must explain what the GPU computes, rather than assume
that an operator call already has the right answer. The local cell calculation
uses five phases separated by barriers. Each lane computes one matrix entry,
with a sequential sequence of multiply and add operations. The proof relates
that ordered calculation to the actual TorchLean matrix-product definition.
It must not rearrange rounded sums using identities valid only over real numbers.

Assembly adds the contributions for a global node in element order. Filtering
other nodes' contributions out of that order must preserve its value even when
addition is not associative. Writes to different nodes may be scheduled in any
order because each node has one writer.

The GPU's dot product partitions inputs among 256 lanes, then combines partial
sums in a tree. That ordering belongs to its numerical specification. Agreement
with a sequential CPU dot product is not a universal bitwise property. The
solver must be related to its own rounded operations and fresh residual check;
a different iteration history is not itself a correctness failure.

Binary64 arithmetic uses the pinned Lean logical Float model. FloatLib supplies
the exact dyadic decoding used by the residual checker and proved arithmetic
bridges under explicit finiteness conditions.
Those logical bridges do not themselves establish the behavior of a compiler
or physical GPU.

The final instruction-level connection must cover fetched instructions, register
updates, byte addresses and bounds, shared-memory barriers, assembly ownership,
and the host launch sequence. Relating a phase calculation to TorchLean alone
does not discharge these obligations. Completed lemmas state their own scope;
missing layers remain explicit rather than becoming theorem hypotheses asserting
the correspondence they are meant to establish.

The accepted whole-solver guarantee is an a posteriori residual certificate: a
check of the actual returned solution, independent of how the solver obtained
it. Exact rational arithmetic interprets the saved binary64 basis, derivative,
weight, load and solution words. NaNs, infinities, malformed shapes and altered
uniform connectivity are rejected. The coefficient values are the represented
setup values, not ideal quadrature recomputed over real numbers.

Acceptance requires zero boundary values and
`‖b − A x‖₂ ≤ max(atol, rtol · ‖b‖₂)` on interior nodes, where A uses the
TorchLean tensor operator in exact arithmetic. The check compares squared
rational quantities, avoiding any rounded square root or empirical allowance.
The soundness theorem applies to every accepted vector and does not assume
PTX correctness, PCG convergence or agreement with the CPU iteration history.
All rounding in the returned solution is included by checking its exact stored
values. Successful GPU status alone is insufficient for acceptance.

This establishes a result certificate, not an instruction-refinement theorem.
It does not prove that every GPU execution will terminate or pass the check,
and it gives no continuous PDE error or conditioning-based solution-error bound.
Compiled checker execution, input/output transport, and a particular saved GPU
run retain their stated runtime and provenance boundaries.

Instruction correspondence is proved from fetched code and its initial storage.
Binary64 loads and stores use eight little-endian bytes, with explicit alignment,
allocation bounds and nonwrapping addresses. Arithmetic preserves the supported
rounding behavior and treats NaN payload freedom separately from a canonical
Lean value. A completed execution must derive each observed output from these
steps; a premise that a phase already computes the tensor formula is insufficient.
The program checked by a theorem must also be tied to the emitted PTX, including
its predicates, integer indexing, branches and synchronization instructions.

The complete `true_residual` entry has a per-thread instruction proof. It loads
the actual right-hand-side and operator-result bytes, subtracts their binary64
values, and stores the corresponding TorchLean tensor-subtraction coordinate.
The proof includes parameter and thread-index reads, the out-of-range return,
execution existence, allocation bounds, and preservation of bytes outside the
one output word. It does not assume that the operator-result input equals A x.
Contiguous-array addresses are derived from the arena base and field offsets.
A checked frontend compares the proved instruction list with emitted PTX.

Parallel residual verification permits each eight-byte load to choose a candidate
word before checking its memory sources. Each byte must come from the initial
storage or a matching byte of an actual executed store. The executed instruction
trace supplies every store's calculated address and operand value. If the output
array is disjoint from both inputs, no thread can supply a store to an input
byte. Every input load must therefore recover its initial word, independently
of thread order or a freedom to combine byte sources.

For this closed launch, with no concurrent external writer or address alias,
the resulting output tensor equals TorchLean binary64 tensor subtraction.
The 256-thread index calculation is nonwrapping in the bounded array layout;
each active lane owns one disjoint output word. Padding lanes return without
memory accesses. Publishing the actual stores in any order yields the same
decoded output and preserves every byte outside the outputs. A witness supplies
successful fetched executions and compatible initial-byte sources.

The parallel proof uses necessary source constraints, allowing more candidates
than the complete PTX memory rules. A universal result over those candidates
therefore needs no sequential-consistency assumption. The witness is an
execution of this broader candidate model, not a full PTX admission or hardware
progress theorem. Publication describes storage after the completed stores; the
CUDA host-visibility mechanism is not proved. The complete cell, assembly, reductions, remaining PCG kernels and host launch
composition still need their instruction-level connections. The three middle
cell phases have the stronger instruction theorem described below. No premise that these phases
already compute their specified answers substitutes for that work.


The eight unrolled cell contractions have local fetched-instruction proofs.
Each operand comes from its actual global or shared byte address, using row-major
indexing and explicit allocation bounds. The accumulator starts at positive zero
and performs separate rounded multiply and add operations in increasing
inner-index order. Every completed block equals the TorchLean matrix product of
the corresponding byte-backed row and column views, and a valid initial snapshot
has a completed execution. Decoded NaN equality preserves encoding freedom.

The layout proof supplies aligned, in-bounds, nonwrapping addresses from complete
allocated matrices and in-range coordinate operands for Q1 through Q4. Integer
index instructions retain their modular semantics outside those conditions.
The local block preserves the global/shared memories, their allocation bounds,
and the base and row/column registers. Both generated accumulators are covered.
A checked frontend compares all eight blocks in each element entry with the same
Lean instruction programs used by the proofs.

These local contraction contracts use supplied phase snapshots. They do not
establish that prior stores and barriers provide those snapshots. The middle-slice theorem below discharges its control, weight and barrier
obligations. The consumer extension below justifies final reads; initial gather,
concurrent output-tail composition and complete parallel admission remain to be
connected for the full cell. A hypothesis that
a previous phase already computes its matrix answer cannot replace that work.

Shared-plane publication connects a lane's register result to its eight stored
bytes. The three actual instructions widen the lane index, add the shared base,
and store at the plane offset. Bounds derive from the seven-plane allocation
and the active lane range; scratch address registers cannot replace the value
being stored. A contraction followed immediately by its store publishes the
TorchLean matrix-product coordinate, with a completed execution witness.

A plane contains one word per active lane. Distinct lanes and distinct planes
have disjoint byte ranges. Combining these actual store effects in any order
recovers every producer's word and preserves all bytes outside the plane.
This constructs the concrete snapshot for later matrix loads; it does not yet
prove that a concurrent load observes that snapshot. The remaining full-cell barrier
obligation is to instantiate the reusable arrival, completion and read-source
results with every generated phase, including inactive lanes and repeated use.
No assumed phase answer or assumed snapshot-visibility result closes that gap.

Barrier reasoning uses fetched binary64 candidate executions: a load may choose
an arbitrary eight-byte word before memory-source constraints are checked.
Ordinary arithmetic and stores retain their instruction contracts. A waiting
thread cannot execute another instruction. Barrier zero records its instruction
site and reuse number, and releases only after every participant arrives at that
same site. Completion must have actual arrivals in the recorded history.

For a shared location with one program writer, a completed barrier between that
write and a later read excludes the initial bytes as sources. Matching byte
addresses and the absence of any other writer then force all eight read bytes
to come from that store. This is a necessary memory constraint for the reviewed
whole-block barrier fragment, not a full PTX admission procedure. Its connection
to each generated cell phase must identify the actual store, intervening arrivals
and completion, and subsequent load; a caller-supplied phase-result equality
cannot replace those obligations.

The concurrent fragment is restricted to resource zero and whole-block barriers
without early exits. Its combined padding guard uses a fixed thread-index
comparison; arbitrary predicate changes and the complete kernel prologue remain
outside that abstraction. Candidate loads obtain values from the source relation,
not from a shared sequentially consistent memory. Execution witnesses and
negative examples check that this separation admits the expected value while
rejecting old initial bytes only when the barrier constraint applies.

The emitted cell code is checked for five matching guard/label pairs, four
unpredicated barriers outside the skipped bodies, and no internal control
transfer or change to the activity predicate. This text check does not prove
that all phase bodies refine the concurrent machine. The full-cell proof must
still derive the observed ordering paths and unique-writer coverage from its
complete execution; the middle-slice instantiation below covers three phases.

If no branch can jump past a barrier, every access at a later instruction position
has an actual completion and arrivals from all threads in its earlier execution
history. This ordering theorem holds for arbitrary schedules and candidate load
values. The condition concerns branch targets, not memory values or a presumed
phase result. The full generated cell must instantiate these branch conditions and identify
the instructions that produce and consume each plane.

Producer ordering also follows from fetched execution. For an active writer,
a guard before its required store either executes the body or lands no later
than that store. Crossing the store instruction therefore records the actual
write before the writer reaches the barrier. Event positions connect this write,
the writer's arrival, the common completion and a later read in strict order.
Forward-only control also prevents a thread from executing the same store site
twice. Combining this fact with the shared-plane address layout supplies storage
ownership without assuming a phase's computed value. The middle slice instantiates these conditions below. The complete generated
cell still needs the gather and index/store/return tail joined to the concurrent
arithmetic fragment.

The three middle arithmetic phases have a concrete concurrent instruction
program, including their padding branches, weighted contractions, six shared
stores and three barriers. Starting immediately after the gathered-input barrier
keeps the earlier gather outside this slice. The initial shared bytes remain
explicit input storage; they are not assumed to equal a tensor answer.

Shared-store address coverage is derived from the executed widening and base
addition instructions. A small check of the program's instruction sequence tracks
when those two scratch registers are ready for a store; branch targets cannot
enter halfway through that preparation. The shared base and lane registers stay
unchanged, and inactive lanes cannot enter a data instruction. These facts turn
the concrete slice's store records into the plane-ownership contract. The whole-slice numerical proof connects candidate loads and those stored
words to the ordered TorchLean arithmetic. The complete gather and concurrent final-output composition
remain separate obligations.

The structural certificates cover Q1 through Q4 with the emitted arena layout:
for matrix width m, the basis starts at offset zero, the derivative at 8m²+32
bytes and the weights at 16m²+64 bytes. Other layouts require another certificate.
The certificates are checked by Lean's kernel, independently of the frontend
that compares the complete phase bodies and guards with emitted PTX.

For this slice, address coverage and store non-repetition give each shared word
a unique producer. A read of that word after the relevant barrier recovers the
actual producer's stored bytes under the stated necessary source constraints.
No assumed coverage or barrier-ordering relation is supplied for the execution.
The numerical theorem below identifies each stored decoded value with its
TorchLean coordinate.
A finite Q1 candidate run completes all three barriers with four active and 28
padding lanes. Its actual load choices and computed store words satisfy both
necessary byte-source constraints. This witnesses the completed numerical
theorem without an assumed phase value. It remains separate from arbitrary-input
execution existence, full PTX admission and hardware progress. Negative code
checks reject a changed matrix coordinate and replacing weight multiplication
with addition.

Within the middle slice, the later reads consume planes 1 through 4. Planes 5
and 6 are produced here and consumed by the final arithmetic extension below.
That extension proves their publication to actual final reads; output-tail
interleaving remains part of complete cell composition.

The numerical connection projects a thread's actual interleaved execution of a
straight-line contraction onto the existing scalar instruction proof. Its memory
view contains byte values justified for that phase; it must not replace arbitrary
loads with a desired answer. Each load in the projected interval must agree with
that view, while instruction positions, registers, allocation bounds and rounded
arithmetic come from the concurrent execution. Other threads may run between
these instructions. This bridge supplies the ordered TorchLean contraction once
the phase's byte-source obligations have been discharged.

For the middle slice, global coefficient storage and shared plane zero have no
writers. Compatible byte sources therefore force their reads to recover the
initial bytes, independently of scheduling. This does not prove how the omitted
gather established plane zero. Reads of intermediate planes instead require the
actual producer and barrier-publication results; initial bytes cannot substitute
for those computed values.

The replayed contraction also determines the word emitted by the real shared
store. The two preceding address instructions preserve the accumulator. A
subsequent read recovers the decoded computed value when the separate publication
proof identifies that store as its source. This reusable result complements the
whole-slice symbolic proof below. A nonzero two-thread
example checks the replay and actual-store connection with compatible sources;
a wrong read from read-only bytes is rejected.

Whole-slice numerical composition uses symbolic register expressions as proof
bookkeeping: a record of how each value was calculated. A soundness theorem
relates these expressions to actual fetched instructions under any interleaving.
Address tracking discards loaded values, so locating a read does not assume that
its value is already correct. Kernel-checked certificates identify every read's
region and every store's exact matrix expression for Q1 through Q4.

The word view used by the proof reads coefficients and plane zero from initial
bytes. For intermediate planes it selects an actual store event. The control,
ownership and barrier proofs establish that each required store exists, is the
only writer, and supplies the later reads. Thus every load agrees with this view
without an assumed per-load value, scalar trace or phase answer. Numerical
tracking then derives each ordered contraction and both weight multiplications.
Decoded floating-point equality retains the permitted freedom in NaN encodings.

Every completed middle-slice execution satisfying the necessary byte-source
constraints produces all six TorchLean intermediate tensors. For every plane
and coordinate, the proof identifies an actual shared store at that coordinate's
byte address and equates its decoded word with the TorchLean value.
The result covers arbitrary initial words and permitted interleavings; no
associativity of rounded addition is used. Each contraction starts at positive
zero and uses increasing inner indices with separate multiplication and addition.
Only the operands of an individual weight multiplication are exchanged.

The entry conditions require all 32 threads at the slice's first instruction,
a reset whole-block barrier, the correct global/shared bases, lane and row/column
registers, and a nonwrapping seven-plane shared allocation. These are explicit
conditions on the omitted prologue and gather. Actual execution supplies valid
memory accesses. The theorem is conditional on completion; it does not assert
termination for arbitrary inputs or a GPU scheduler. The source rules are
necessary constraints, not complete PTX memory admission.

The remaining whole-cell obligations are to establish the gathered input and
entry registers, incorporate the index/store/return tail into the concurrent machine,
and prove the full launch and memory-admission connections. Assembly, reductions,
PCG kernels and host composition retain their separate instruction obligations.

The complete final arithmetic body has a fetched-instruction proof. It computes
two ordered contractions from shared planes 5 and 6, adds their binary64 results,
calculates the element/lane output index, stores eight global bytes and returns.
Every completed run from valid input storage writes the corresponding TorchLean
coordinate. It preserves shared storage and all global bytes outside that word.
A separate theorem constructs a completed run for every such valid snapshot.

The output index is the element number times the number of entries per element,
plus the lane number. The actual 32-bit multiply-add wraps on overflow; bounds
on this expression justify its ordinary natural-number interpretation. The
64-bit byte address additionally requires alignment, allocated output space and
no address wrap. Complete allocated operand matrices discharge all input-load
bounds. These conditions concern storage and indices, not a presumed answer.
For a matrix coordinate (i,j), lane i*m+j supplies the row-major output location;
the local theorem retains the actual lane and element registers as inputs.

A phase-by-phase theorem connects actual middle-run stores to this final output.
It constructs the final shared bytes from those stores, proves that each aligned
eight-byte load recovers the recorded word, and then composes the final fetched
execution with the six proved middle-plane equations. The stored result equals
the complete TorchLean local cell calculation on the initial coefficient and
shared-input tensors. No premise asserts an intermediate or final numerical
answer. Under valid final storage, the composition also constructs a completed
final run with that result. The final phase's base, coordinate and index registers and allocation
conditions are still explicit entry conditions.

This composition uses a constructed snapshot. It does not yet prove that the
final reads obtain those bytes within a single concurrent whole-cell execution.
The concurrent consumer extension below supplies the actual read-source argument
for the arithmetic fragment. Initial gather, concurrent output-tail composition,
full launch admission and host visibility remain separate from that result.

The frontend compares the complete final body and return in all three element
entries with the Lean program used by these proofs. Kernel-checked examples
exercise nonzero, asymmetric matrices and a nonzero element/lane output offset;
wrong addition, short or unaligned output storage, and index overflow have
explicit checks. These checks support the general proofs and text binding;
they are not a new GPU experiment or hardware-conformance claim.


The concurrent arithmetic extension includes the final two contractions and
addition after the middle phases' last barrier. It uses the same fetched
candidate machine: loads may choose arbitrary words before their byte sources
are checked. One source assignment covers the entire middle and final history.
Final shared loads address planes 5 or 6 after the actual completed barrier.
Derived store ownership and barrier ordering force each load to recover its
unique producer's recorded bytes; initial bytes cannot replace that producer.

The theorem takes an actual completed middle execution and its continuation
from the same boundary state, at the existing last barrier. Lifting and joining
these runs gives one fetched concurrent execution; no new barrier or memory
snapshot is inserted. The continuation contains no stores. Therefore it cannot
supply a new source for an earlier read, and the required middle-prefix source
constraints follow from the whole-history constraints. They are not separate
assumptions permitting unrelated accounts of memory.

The real final arithmetic register equals the complete ordered TorchLean local
cell calculation. Sound symbolic tracking follows the fetched operations and
justified candidate loads, preserving rounding order and NaN encoding freedom.
The existing fetched index/store/return proof starts from that actual concurrent
result state and establishes the global output value. Its storage bounds remain
explicit; the result does not depend on constructing a replacement input memory.

This concurrent fragment stops after arithmetic. The integer index, global
store and return still use the separate fetched model. Their interleaving with
other final readers, automatic extraction of the supplied execution boundary
from an arbitrary complete kernel run, prologue/gather, full launch composition
and complete memory admission remain open. Inactive lanes skip the arithmetic
to its cutoff; correspondence of the omitted tail and actual return belongs to
the remaining full-kernel connection. No hardware progress claim follows.

A completed zero-data Q1 execution witnesses the whole-history source conditions
and final result with all 32 participants, including 28 padding lanes. This is
finite existence evidence, not an arbitrary-input termination theorem. A changed
final addition fails the symbolic numerical certificate. The existing nonzero
final-body checks and saved-PTX bindings remain separate regression evidence.
