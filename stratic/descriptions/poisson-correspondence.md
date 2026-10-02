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
CUDA host-visibility mechanism is not proved. Concurrent assembly publication, reductions, remaining PCG kernels and host
launch composition still need their instruction-level connections. The complete
cell entry and the isolated assembly traversal have the stronger instruction
theorems described below. Their output values follow from executed instructions.


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

The theorem takes one actual concurrent run. It derives the split at the last
middle barrier from fetched instructions: branches cannot skip this barrier,
and releasing it places every participant immediately after it. The prefix
therefore completes the middle program, and the remaining steps are its actual
continuation. No boundary state, schedule, extra barrier or memory snapshot is
assumed. Only the output thread under consideration must have finished final
arithmetic; other threads may still be computing. Lifting and joining
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

The arithmetic fragment remains useful as an intermediate proof model. A
combined concurrent machine now continues each thread through integer indexing,
the global store and return. It reuses the arithmetic/barrier rules before the
cutoff and the existing fetched instruction rules afterwards. The machine stores
only actual thread states, predicate bits and return flags; it does not contain
an assumed arithmetic execution. Returned threads cannot step again. Inactive
final lanes branch past all output operations to the actual return.

A completed zero-data Q1 execution witnesses the whole-history source conditions
and final result with all 32 participants, including 28 padding lanes. This is
finite existence evidence, not an arbitrary-input termination theorem. A changed
final addition fails the symbolic numerical certificate. The existing nonzero
final-body checks and saved-PTX bindings remain separate regression evidence.

Output stores may be interleaved with another thread's coefficient reads. The
memory-source proof can remove those stores from a history if they touch none
of the bytes read by the retained instructions. It keeps the remaining events
in their original order and renumbers each chosen store source to its retained
position. Two identical-looking store records still have distinct positions.
This restriction preserves both byte-source compatibility and the requirement
that a write published through a barrier cannot be replaced by initial bytes.
It does not choose a fresh, unrelated account of memory.

For Q1–Q4, instruction certificates and symbolic address tracking place every
actual global read inside the region containing B, D and W. The region includes
the gaps between those tables, and the bound covers all eight bytes of each
read. A nonwrapping global base is required. The final integer index and byte
address calculations place output words beyond this region when the output
offset is at or beyond its end. This requires the existing 32-bit index bound
and 64-bit address bound; modular wraparound is not ignored. The fetched
index/store/return tail preserves every coefficient byte. Distinct bounded
output indices also give disjoint eight-byte output words. The saved-PTX binding
checker verifies separated coefficient/output extents, rejecting overlap.

From a combined execution, the proof derives its arithmetic run, retained event
positions and arithmetic-result register relation. Every omitted event is a
global output store; this follows from the concrete six-instruction tail.
Arithmetic threads match their projected state exactly. Threads already in the
tail may change scratch registers and output bytes while preserving register 11.
A barrier release requires all participants at the same live barrier, so it
cannot silently advance a thread already in its tail. This argument allows any
schedule admitted by the combined machine and inserts no extra barrier.

The resulting numerical theorem relates an actual thread's register 11 to the
ordered TorchLean local cell result once that thread reaches the tail. It uses
one whole-history source assignment and derives every actual global-store
address from the launch registers. The base, lane and cell registers are
preserved throughout the combined run. The four index/address steps establish
the store address at its actual fetched instruction. No later event-address
bound or desired numerical value is supplied as a premise.
Regression histories preserve a shared producer across renumbering and reject
an omitted store that overlaps a retained read by just one byte. These histories
check the source transformation; they are not new GPU or whole-kernel witnesses.

A kernel-checked zero-data Q1 execution includes all 32 threads and the real
output tail. One lane stores and returns before another lane performs its
remaining coefficient reads. Exactly four global output stores occur; all
28 padding lanes return without storing. Its event addresses, zero words and
whole-history source constraints satisfy the combined numerical theorem.
This is finite existence evidence, not arbitrary-input termination or complete
PTX memory admission. The omitted prologue/gather, launch composition, assembly,
reductions and complete solver instruction correspondence remain open.

The launch layout places the output offset at or beyond the end of the
coefficient region. Its bounds require the natural cell/lane index to fit in
32 bits and the widened byte address to fit in 64 bits. The current interface
conservatively checks these arithmetic bounds for all 32 lanes, including
padding lanes; it does not require their unused output words to be allocated.
These conditions imply the coefficient base does not wrap and every actual
global store is beyond the coefficients. Allocation and alignment are checked
by the actual store instruction. With a common cell ID, different launch lane
IDs also imply disjoint eight-byte output words for their actual stores.

After an active lane executes its store, reading its output word from that
lane's actual byte memory yields the TorchLean local cell value. This holds
in the same interleaved execution, even if other lanes have not completed.
The result follows from the store's byte update and preservation through
return; a separate tail run or memory snapshot is not assumed. The actual
recorded stores also compose into one global output tensor. Host-visible
completion and full memory admission remain distinct obligations.

Checks instantiate the stored-value theorem in the completed Q1 concurrent
witness using launch conditions alone. A separate fetched tail checks nonzero
base, cell and lane indices and a nonzero stored word. Mutated launch bounds
reject 32-bit index overflow and 64-bit byte-address overflow.

Global output publication uses the actual recorded global stores. A completed
active lane is proved to have emitted its store: without that event, its program
counter cannot pass the store instruction. The recorded word equals the lane's
final arithmetic register because later steps preserve that register. No list
of required stores or desired output words is supplied as an assumption.

Publishing an event history means applying its global store records to one byte
memory; loads, shared accesses and barriers leave that memory unchanged. Every
store either belongs to the chosen output lane and writes its proved word, or
has disjoint bytes because it belongs to another lane. The resulting output
word is therefore independent of publication order and of the old output bytes.
Bytes outside the output words remain unchanged. This mathematical merge does
not assert CUDA host visibility or full PTX memory admission.

If all active lanes have passed their stores, the ordinary row-major tensor
view of the published bytes equals the ordered TorchLean local cell calculation.
Its address is the launch base plus the cell offset, output offset and eight
times the row-major coordinate. The theorem applies to every combined Q1–Q4
execution satisfying the stated launch bounds and necessary byte-source
constraints. Permuting records only changes their publication order; source
constraints still concern the original execution history.

The completed Q1 witness instantiates the whole-tensor theorem for arbitrary
old output bytes and for reversed publication order. The nonzero fetched tail
checks publication of its actual recorded word. Negative checks reject a missing
store and partially overlapping store bytes; distinct addresses alone do not
justify disjoint words. These checks do not establish arbitrary-input execution
existence or the omitted whole-kernel stages.

The element-kernel prologue establishes its register setup by executing the
seven emitted instructions before the first gather guard. The launch context
supplies the arena parameter, the address of the allocated scratch array within
shared memory, the thread index and the cell index. The program copies those
addresses and indices, marks lanes below width squared as active, and computes
the row and column by unsigned division and remainder. The 32-bit values occupy
zero-extended words in the common register container.

From any initial registers and bytes, a positive width whose square fits in
32 bits gives a seven-step fetched execution starting at program counter zero.
Every such execution has the explicitly computed final state at counter seven.
All array bytes, allocation metadata and unrelated registers are preserved.
For active lanes, both coordinates are within the cell, and row times width
plus column reconstructs the lane index. For the 32-thread launch, the result
derives the six register values used by the arithmetic entry contract.

The prefix ends before gather, not at a kernel return. It does not reset a
program counter or install gathered bytes to identify this state with the
post-gather arithmetic entry. The active gather now has a separate fetched snapshot proof;
concurrent gather now also has a prefix theorem. Visibility to later arithmetic
and composition with that continuation remain execution obligations. Shared-symbol resolution,
parameter passing and special-register inputs are launch context assumptions,
not a CUDA driver/ABI theorem. Zero divisors are outside this bounded fragment;
PTX does not specify a unique result for them.

The semantic review uses the pinned PTX 9.4 source for the selected unsigned
forms, special-register moves and shared-symbol address move. The Lean renderer
uses the same instruction list as the fetched proof. A separate source-binding
check compares the complete entry declarations and seven instructions against
the emitted kernels, rejecting added instructions, wrong register types,
misaligned scratch declarations, wrong indices or predicate boundaries. Neither
text equality nor Lean checking alone proves semantic fidelity or hardware
conformance. The bounded prefix is not complete instruction-family coverage.

Kernel-checked examples cover all 32 lanes at widths two through five with
nonzero initial registers and bytes. They also check the maximum unsigned lane,
wrong initial counter, unsupported zero divisor and mutations to the row and
active-lane computations.

Gathering a cell input must read each connectivity entry as exactly four
little-endian bytes, interpret it as an unsigned node index, then read the
corresponding eight-byte source value and store its unchanged bits in shared
memory. Four-byte bounds and alignment must be checked separately from the
eight-byte value accesses; adjacent connectivity entries must not be treated as
one oversized load. The address calculation must retain modular integer
semantics, with ordinary nonwrapping array bounds establishing the intended
layout. The gather must preserve the prologue registers needed by arithmetic.

The twelve active gather instructions have a fetched execution proof for arbitrary
source bits, including NaN payloads and signed zero. They derive the node index
from the actual four-byte connectivity entry, load the corresponding source
word and store it into the lane's shared slot. Allocation sizes, alignment,
nonwrapping addresses, a valid cell and lane, and connectivity entries within
the source vector imply every access is valid. The gathered word and unchanged
base, cell, lane, row and column registers follow from execution.

The decoded shared word equals the corresponding entry of TorchLean's cell
gather when initial connectivity and source bytes represent the input arrays.
These are input representation conditions, not assumptions about the output.
This local theorem reads a fixed input memory. A separate concurrent prefix
theorem below establishes its input reads and barrier control; visibility to
later arithmetic still needs the combined execution history.

The typed gather program also renders the complete guarded body for each of
the three source vectors. Binding checks reject incorrect load width, index
stride, source index, shared destination, extra instructions or a missing first
barrier. Kernel checks cover four-byte-only allocations, adjacent index entries,
unaligned or truncated indices and out-of-range nodes. Bit-copy checks include
nonzero cells, lanes and base addresses and unusual floating-point encodings.

Concurrent gathering must justify both load sizes from actual execution records.
Each connectivity byte may name initialization or a byte of a recorded store;
an eight-byte store overlapping only part of an index still counts. If no global
store covers the input bytes, source compatibility must force the original
input word. The four-byte read records can be kept separately from the existing
eight-byte/barrier history because they neither write memory nor synchronize.
Their sources still refer to actual stores in that history. This restricted
representation covers unsigned global index reads, not general mixed-width PTX.
The entry must then execute the prologue, active-lane branch, gather and first
barrier, deriving the arithmetic entry state and shared input without assuming
the gathered answer or a completed barrier.

The concurrent entry executes the emitted setup at counters zero through six,
the active-lane branch at seven, the twelve gather instructions at eight through
nineteen, and the full-block barrier at twenty. Waiting threads cannot execute
another instruction. Every input load initially chooses arbitrary bits. The
executed prefix has no global stores, so byte-source compatibility forces all
connectivity and source-vector reads to their initial bytes, including partial
byte overlaps. It does not impose a single source on an entire word.

From that concurrent history, the proof derives each lane's local instruction
trace. An active lane that reaches counter twenty-one has stored exactly its
TorchLean cell input; padding lanes follow the actual branch. Crossing counter
twenty requires a genuine barrier release, advances every participant to
twenty-one and resets the used barrier generation. No completed barrier or
ready shared tensor is supplied as a premise.

The base, lane, row and column registers and the actual barrier state establish
the arithmetic entry contract. Re-expressing instruction counters relative to
the next instruction preserves all registers, bytes and allocation metadata.
This change of numbering does not execute instructions or install shared values.
The actual gathered store records now determine the continuation's plane-zero
loads using their joint history and synchronization.
The current prefix source argument also needs extension to exclude later output
stores from the input bytes when the whole entry and body are composed.

A completed 32-thread Q1 witness uses nonzero arena and shared bases, cell one,
nonidentity connectivity, ordinary values, signed zero and a NaN payload. Its
word and index sources are checked, and the general arithmetic-entry theorem
is instantiated on that run. Omitting the last participant prevents release;
wrong index values and overlapping mixed-size accesses fail their checks.
This witness establishes a permitted candidate in the stated source model,
not arbitrary-input existence or full PTX admission. The complete twenty-one
instruction prefix and its label are bound to all three emitted element entries.

Shared publication must use recorded gather stores from the actual entry run.
Every completed active lane must have emitted its store; a list of required
stores is not an input assumption. Each record must have the lane's derived
shared address and copied bits. Later prefix steps preserve that stored value,
and distinct active lanes own disjoint words. These facts must supply the
producer side of the first-barrier visibility argument.

The producer theorem now derives a store record for every completed active lane.
It follows the actual branch and instruction counter: an active lane cannot
reach completion while avoiding the store, and a padding lane cannot reach that
instruction. This argument is independent of whether the old shared bytes
happen to equal the desired result.

Every recorded gather store uses counter nineteen, the shared-memory base plus
eight times its lane index, and the word read through that lane's connectivity
entry. Once a lane passes the store, its remaining prefix steps preserve all
of its data except the instruction counter. The recorded bits therefore equal
the proved final gather value. Decoding an actual record yields the corresponding
TorchLean cell-input entry under the same input representation conditions.

The address calculation and allocation bounds also establish byte ownership.
Distinct lane IDs produce disjoint eight-byte slots. A store covering a byte of
one slot must come from that lane, at the same byte offset, and must contain its
proved word. Coverage, padding exclusion and these ownership results are
instantiated on the nonzero 32-thread witness. The producer theorem alone is not a visibility claim; the following barrier
argument connects its records to actual continuation reads.

The first barrier's history must be derived from its actual requests. Starting
from a reset barrier, every completion must have earlier arrivals by every
participant. Each gathered store must precede its writer's arrival, and therefore
the completion. A subsequent shared read can then use these actual records and
the necessary byte-source rules to exclude stale initialization. This reasoning
must preserve byte-level source freedom and must not assume a desired read value.

Starting from a reset barrier, the entry history proves that every observed
completion has earlier real arrivals by all thirty-two participants. A gather
store is before its writer's arrival: after reaching the barrier, that lane
cannot execute another store in the prefix. The same barrier transition and
history rules are reused by the entry and arithmetic machines.

The arithmetic body stores only in shared planes one through six; plane zero
holds the gathered inputs. Its output tail adds only global stores. Actual
shared stores in the continuation therefore cannot overwrite any gathered slot.
This preservation depends on fetched instructions and derived addresses, and
does not assume a correct arithmetic value.

For an actual prefix followed by an actual arithmetic/output run, every shared
read of a gathered slot equals that slot's proved gathered word. The proof
derives store-before-arrival-before-completion order and excludes stale initial
bytes through the necessary performed-write rule. Byte sources remain independent:
all covering stores have the same relevant byte, so whole-word atomicity and
a unique chosen event are unnecessary assumptions.

The modular visibility theorem takes prefix input-source constraints. The
joint-history theorem derives them from the actual prefix and continuation,
using the input/output layout separation described below. The body numerical
theorem uses an initial-byte view proved from the actual gathered producers.
Neither step assumes a desired read value. Whole-entry execution composition, general execution existence, assembly,
reductions and solver/launch composition remain separate obligations.

The nonzero Q1 regression proves the order of every active producer before its
real barrier completion. An appended shared observation must see the gathered
minus-two bit pattern, and the old repeated-byte pattern is rejected. This
observation check exercises the memory interface; it does not claim a fetched
arithmetic execution for the appended test record.

To compose the numerical result, the continuation's proof may use a starting
byte view assembled from completed gather stores. This view must be proved to
agree with every recorded prefix store and to preserve untouched bytes. Source
rebasing must map those prefix-store origins to initialization, retain later
store origins with corrected event indices, and preserve both compatibility and
performed-write constraints. The actual execution state is not replaced. The
assembled input tensor must agree with TorchLean gathering under explicit input
array representation and memory-layout conditions.

The arithmetic proof's starting byte view is now constructed from the real
post-gather lane memories. Every recorded gather store agrees with this view
byte for byte, and bytes outside the gathered slots retain their original
initialization. The view is a description used in the proof; the actual lane
states, including their old copies of other lanes' shared bytes, are unchanged.

A source-rebasing theorem carries the joint history into the arithmetic proof.
A byte supplied by a real pre-barrier store becomes an initial byte of that
proof view. Sources from later stores keep their byte offsets and receive
shifted event positions. A read which originally chose initialization cannot
cover an earlier performed gather store. Later shared writes are disjoint from
those stores, so the continuation also retains its performed-write constraints.
No desired read value or completed tensor is a premise of this rebasing.

The rebased shared-input tensor equals TorchLean's connectivity gather when
initial index and source arrays represent that input. Cell and lane coordinates
are derived from the launch context. Combining this fact with the existing
arithmetic proof establishes the actual result register and the published
whole-cell output tensor, independently of output-record publication order.
Its coefficient tensors are the decoded initial arena tables. The operator
representation theorem below relates them to the stated TorchLean operator;
it does not certify how an external host generated or serialized the tables.

A single execution of the complete cell entry now derives the first-barrier
split and both fetched subruns. Instruction counters stay absolute in the
execution: arithmetic starts at counter 21. The proof translates its local
view in both directions, including branch destinations, data records and
barrier sites. A barrier generation counts completed uses of the barrier;
events before and after the first release use different generations, so
translating later sites leaves the earlier barrier's identity unchanged.
This transports the byte-source conditions without supplying computed values.
The resulting theorem publishes the TorchLean cell tensor from the full run's
actual global-store history. Layout, represented input arrays, necessary
byte-source admission and completion of the active lanes remain explicit
premises. Coefficient tables are still decoded initial inputs.

A nonzero regression continues the actual Q1 entry state through lane two's
first coefficient and shared-input loads. Checked sources make it read lane
zero's minus-two word although lane two's own local shared bytes at that address
still contain the old repeated-byte pattern. The rebased source contract is
instantiated on this real execution. This is a partial body witness, not general
existence of a complete cell or solver run. The finite compatibility checker
proves the existing per-byte relation; performed-write checks remain separate.

Input admission for the complete history must not depend circularly on assuming
that the input reads were already correct. The setup and address-control
registers are established independently of loaded values. The branch guard
excludes padding lanes from gathering. Connectivity addresses are then derived
before admitting the four-byte indices, and source-vector addresses are derived
from those admitted indices. Disjoint input and output arrays exclude later
output stores as byte suppliers. These steps derive the prefix source contract from the joint history without
assuming its input values or the final tensor.

The whole-entry instruction binding compares every emitted instruction through
return and the absolute counters of all branches and barriers against the Lean
program lists. It rejects a shifted barrier site or an incorrect return target.
A nonzero partial witness checks cross-lane gathering with absolute counters.
A separate zero-data Q1 witness reaches all 32 returns and publishes four
outputs, with checked index, word-source and performed-write admission. These
finite witnesses establish existence for their inputs; arbitrary-input
execution existence and the remaining solver launches are separate obligations.

The complete cell theorem names the operator whose coefficients were uploaded.
A representation contract relates each initial binary64 word of the B, D and W
tables to the corresponding TorchLean coefficient, and requires equal numbers
of quadrature points and interpolation nodes for this square-table kernel.
The proof preserves the ordered calculation when transporting tensor dimensions
and concludes equality with that operator's localAction. This is an input
representation contract, not an assumption about the computed output. External
host generation and serialization of those tables are not proved by it.

Assembly uses one thread per global mesh node. Each thread reads a pair of
offsets delimiting that node's list of contributing cell entries, then adds
those entries in their stored order. The traversal must be proved from actual
unsigned index loads, comparison, conditional branch, increment and backward
branch instructions. The offset list preserves the reference's element-major
order; floating-point addition is not reassociated. Boundary masking and the
final global store are part of the fetched program. The initial memory view
and its separation from outputs must remain explicit until launch composition
justifies them. A reusable control-flow interpreter should support these loops
without installing a loop result or iteration count as an execution premise.

The assembly traversal loop now has correctness and execution-existence
proofs. Every completed fetched execution performs the ordered left fold over
its initial cursor range, including its actual four-byte contribution indices
and eight-byte values. A physical layout of the two allocated input arrays,
with every index in range, discharges all access premises. If the cursor starts
at or before the unsigned end index, each iteration advances it without wrap,
so a returning execution exists. No iteration count, read value or result is
assumed. The proof uses a read-only memory snapshot for this loop slice.

The isolated loop theorem returns at the exit label. The complete entry proof
instead cuts the actual execution at that label and follows its real optional
boundary-mask and output-store instructions. Concurrent publication and
inter-launch memory visibility remain separate from this snapshot execution.
A nonzero kernel-checked witness sums the same three contributions in two
orders and obtains different results, exercising the reason for preserving
floating-point order. Empty-list, insufficient-fuel and invalid-index checks
exercise completion and failure behavior. Fuel is only a bound on executable
witness search; it is absent from the relational correctness theorem.

The complete assembly entry now has correctness and general execution-existence
proofs. Starting at the first instruction, an active thread computes its node
index from the launch context and loads the two offsets that delimit its
contribution list. Its actual branches use absolute instruction positions.
The proof derives the loop entry and exit from that single execution, then
follows the real boundary-mask and output-store instructions through return.
The final byte memory is exactly the initial memory with the computed word
written at the node's address; all other bytes are preserved. A padded thread
returns at the initial guard without any array access or memory change.

The premises describe input memory: the two offset loads, allocated index and
value arrays, an ordered cursor range, and valid boundary/output addresses.
Setup and loop-entry states appearing in these premises are pure functions of
the raw initial state, not supplied executions or desired intermediate values.
The represented index list fixes the order of rounded additions. Every safe
ordered range has a finite returning execution, without a fuel assumption.
This entry theorem uses a per-thread memory snapshot. The parallel theorem
below derives that snapshot from source-constrained execution and publishes
actual stores. Serialized mesh representation and inter-launch visibility
remain separate obligations.

The exact-code checker binds both complete emitted assembly entries, their
register declarations, launch shapes and absolute branch destinations to the
Lean instruction lists. Kernel-checked full-entry examples exercise nonzero
cancellation in two orders, boundary masking, padded return with no allocation,
and rejection of invalid offset, value and output accesses. These checks and
the instruction proofs are distinct from testing or validating GPU hardware.

Assembly access safety now follows from the physical array layout and the
ordinary 256-thread node indexing. The arena contract specifies nonwrapping
allocation, field alignment and extents, and the host layout's node-count bound.
Initial index bytes must delimit ordered ranges inside the contribution table,
and every contribution index must name an allocated cell value. These input
conditions discharge the complete entry's memory premises and establish a
returning execution for every active node. Distinct nodes have disjoint
eight-byte output slots, including a nonzero arena base.

The entry's stored value equals the ordered sum obtained by reading its index
list and following those indices into the cell-value array, with optional
boundary masking. Filtering an element-major list into one list per mesh node
preserves the exact rounded scatter sum. The connection to a serialized mesh
is an explicit input representation contract on ordered index lists; it does
not assume an output sum. A mathematical publication theorem merges the actual
output words of complete snapshot executions in any order containing every
active node and preserves all other bytes. The parallel theorem below
derives this snapshot view from one admitted joint execution.

The branching execution model also records freely chosen read bits: eight-byte
floating-point loads/stores and four-byte index loads. Arbitrary thread
interleavings project to each thread's actual fetched control flow. Necessary
byte-source checks relate read bytes to initialization or actual recorded
stores. When all recorded stores are disjoint from the read locations, these
checks force the initial read bits and recover the complete snapshot execution,
including loops and stores. The proof maintains local memory agreement across
writes instead of replacing a thread's memory by an assumed snapshot.

For assembly, every recorded store has its owner's node address, independently
of proposed read values. Input arrays occupy byte ranges disjoint from the
output vector; either physical order is allowed. The actual offset-load
addresses therefore force their bytes to initialization. The resulting cursor
bounds constrain each contribution-index load, whose admitted bytes in turn
bound the cell-value address. This dependency order derives every read footprint
from the same joint history and discharges the replay separation condition.
No desired cursor range, read value or local snapshot execution is assumed.

The chronological global stores of that actual interleaving publish the ordered
rounded row sum at each node, with the emitted optional boundary mask. A local
byte changes exactly when its instruction records a global store; other threads
write disjoint node slots. Thus the joint publication agrees with the final
local output word, without assumed store coverage or a supplied publication
schedule. This is mathematical publication of recorded writes, not a CUDA
host-visibility claim.

Every valid physical assembly input also has a returning joint execution with
compatible initialization sources. Each scalar execution reads its inputs
before its sole output store. Its recorded reads therefore use initial bytes;
combining the returning threads constructs an actual admitted interleaving.
This general existence proof does not depend on interpreter fuel or specific
numerical values. Kernel-checked two-node examples instantiate it with nonzero
values, both masking choices, and a nonzero arena base.

Kernel-checked examples exercise two nodes at a nonzero base, masked and
unmasked entry executions, two publication orders, and ordered-scatter equality.
A separate observed execution records an index load, a nonzero floating-point
load and a disjoint output store, with compatible byte sources and successful
replay. The finite source checker rejects a forged floating-point read.

The mesh-to-assembly connection must explain the integer tables rather than
assume each thread receives the desired row. A compressed row table stores all
per-node contribution lists consecutively and records each list's start in an
offset table. Constructing those lists by scanning element-major, row-major
connectivity must preserve the original order. Decoding these serialized input
integers should establish the assembly range/index conditions and recover each
ordered list; it must not assume a floating-point result. The published cell
values can then be substituted into the proved assembly sum to recover the
TorchLean operator, with boundary masking stated separately.

Composing cells with assembly requires an explicit record of each actual cell
execution: initial memory and layout, fetched execution, completed lanes and
admitted byte sources. Such a record may package the existing theorem's
premises, but must not include a desired tensor or output value. Its published
tensor is a proved consequence. Combining cells must also account for inactive
lanes: they return without writing into the next cell's output region.

The compressed-row checker inspects the initial four-byte offset and index
words. Its soundness theorem derives the ordered-row representation and access
bounds. Cell executions share one initial global memory and a contiguous output
array. Every actual global store belongs to an active coordinate of its own
cell; inactive lanes cannot access the following cell's storage. Publishing
these histories preserves the uploaded assembly tables and boundary flags.
Assembly consumes that publication and computes the TorchLean tensor operator
for the actual represented connectivity arrays, without an assumed cell value
or assembled result.

The cell-family composition boundary is explicit. It packages actual per-cell
executions, not an already-proved arbitrary device-wide schedule. Its next
launch starts from mathematical publication of the preceding store histories.
General admitted cell existence, grid scheduling, CUDA transport, external
serialization and remaining solver instructions retain their own obligations.

A nonzero kernel-checked composition exercises this connection. A two-by-two
synthetic cell with identity coefficient matrices, unit weights and unit gathered
values publishes four twos. The uploaded ordered row table directs assembly to
all four values, yielding eight. The cell execution, source checks and assembly
existence proof supply the result; the example does not assume the cell output.
This tests the composition mechanism, not a physical quadrature construction.

Finite witness checking should avoid expanding the same large execution for
every byte. A whole-word checker may compare a read with initialization or a
matching actual store once, provided its soundness proof derives every required
byte-source equality. This optimization is restricted to whole-word source
choices; it neither changes the byte-level contract nor establishes the
separate performed-write condition or complete PTX memory admission.

The tensor operator must also agree with the executable array-based reference.
That connection follows its actual nested element/local-coordinate loops and
in-place array updates, preserving the order of rounded additions. It requires
valid connectivity shape and node bounds, and preserves the reference's vector
length and finiteness checks. A public proof view may expose private helper
computations only with a proved connection to the function actually called;
a second unconnected implementation is insufficient.

The array-reference bridge proves that connection for every well-shaped,
in-bounds mesh with the supported equal quadrature and interpolation dimensions.
It turns the actual nested loops into an ordered fold, relates each array update
to the tensor scatter update, and checks that both enumerate identical local
entries. For a finite vector of the required length, the public Poisson.apply
entry therefore returns the tensor operator's vector. Combined with the actual
unmasked cell/assembly execution, it returns exactly the published PTX vector.
Wrong lengths and nonfinite values retain their original reference errors.
