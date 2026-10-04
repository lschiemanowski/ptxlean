# Poisson PTX execution

The backend solves the same Q1–Q4 unit-square discrete equations as the Lean
reference, retaining binary64 arithmetic. Lean supplies mesh connectivity,
interpolation and derivative tables, integration weights, the load and diagonal.
These setup quantities are transferred once. GPU storage holds the solution,
residual and search directions throughout conjugate-gradient iteration. The CPU
launches stages and reads scalar convergence information at scheduled checks;
it does not compute the repeated operator or vector arithmetic.

One group of GPU threads handles each square element. Successive contractions
apply the one-dimensional basis tables, with barriers separating shared-memory
intermediates. Products and sums use separate explicitly rounded binary64
instructions. Contributions are first written into disjoint element storage.
Every group thread reaches each barrier, including inactive matrix lanes.
A second kernel gives each global node one writer, which sums its incident
contributions in element order. This preserves a deterministic assembly order
without concurrent floating-point updates. Interior solves explicitly zero the
boundary entries; the unrestricted operator is also available for comparison.

Vector updates, division by the Jacobi diagonal, dot products and square roots
are implemented in PTX. Dot products use a specified parallel reduction tree.
Their order can differ from the CPU reference, so numerical agreement is tested
rather than assumed bitwise. The loop retains active and broken state, freezes
updates after recursive convergence, recomputes the true residual at scheduled
checks and at the iteration limit, and restarts if the recursive test was too
optimistic. Empty interiors, zero loads, breakdown and exhausted iterations have
explicit outcomes. The recorded suite does not exercise a restart; implementation
of that branch does not imply observed coverage.

The current hardware target is the RTX 5090. The explicit PTX 9.2 artifact uses
the installed toolchain; the project's semantic target remains PTX 9.4.
Restricted binary64 instruction use is reviewed against NVIDIA's documentation.
Ordinary global and shared loads/stores are weak accesses: synchronization comes
from group barriers and ordered launches, not from the memory operations alone.
The `true_residual` entry has an instruction proof connecting the whole output
tensor to TorchLean subtraction. It derives input values from byte-source
constraints and disjoint output writes, then publishes the actual stores in any
order. The proof assumes a closed launch with no external writer and uses
necessary source conditions rather than a complete memory-admission model.
The three middle cell phases also have the numerical instruction theorem
described below. The complete cell, other kernels and host launch composition
still need their instruction proofs. Compilation and GPU execution retain
separate evidence; no hardware-conformance or continuous PDE theorem is claimed.


Validation covers Q1–Q4, numerical operator comparisons on supplied and varied
vectors, complete solves, polynomial reproduction, boundary preservation,
iteration limits and invalid inputs. CPU references and device results start
from identical setup arrays. Saved cases, PTX and binary hashes, launch records,
outputs, toolchain identity and sanitizer logs make the observations reproducible.
All failures remain visible; tolerances are declared before running comparisons.
No throughput or benchmarking claim is part of this backend.

Generation validates the uniform connectivity, finite setup arrays, positive
interior diagonal, solver controls and a bounded 32-bit index domain. Device
storage contains guard bytes around every buffer; inputs and guards are checked
after solving. These checks and sanitizer runs support the tested executions,
not a universal memory-safety theorem.

The numerical comparison uses fixed absolute and relative tolerances. Rounded
GPU and Lean residual measurements remain diagnostic comparisons and allow a
small measurement discrepancy. Acceptance additionally requires the proved
exact Lean residual checker: the saved setup coefficients and returned solution
must satisfy the requested bound with no extra allowance and exactly zero
boundary values. Iteration-limit and breakdown results are not certified.

Correspondence is established in separate layers. The tensor calculation and
ordered assembly must first agree with the Lean specification without assuming
associativity of rounded addition. A binary64 instruction interpretation must
then connect actual register and memory execution to those calculations. The
parallel dot-product order is part of the GPU algorithm, so the solver's result
is not required to be bitwise identical to the CPU PCG loop.


The eight matrix contractions inside each cell kernel have local instruction
proofs: indexing, byte loads, and ordered rounded operations produce TorchLean
matrix products of byte-backed operand views. Shared-store proofs connect the
computed words to disjoint plane entries.

For the three middle arithmetic phases, the correspondence proof now covers
complete interleaved execution, including padding branches, all six shared
stores, both weight multiplications and three whole-block barriers. Every
completed run satisfying the stated necessary byte-source constraints stores
the six corresponding TorchLean intermediate tensors. Read addresses and values,
producer ownership and barrier ordering are derived from execution; no phase
answer is assumed. The certificates cover the emitted Q1–Q4 arena layouts,
and the frontend compares every body instruction with saved PTX.

The complete final body also has a fetched-instruction proof: two contractions,
rounded addition, element/lane indexing, global store and return. A separate
existence theorem covers valid input snapshots. A phase-by-phase composition
constructs its shared bytes from actual middle-run stores and proves the stored
TorchLean local cell result, with allocation and index conditions explicit.

The middle slice starts with gathered bytes and prepared base/lane/coordinate
registers. The final phase's entry registers are also explicit. The entry prefix now derives the registers and gathered words; visibility of
those words in the arithmetic continuation remains a joint-history obligation. The combined concurrent output tail publishes its actual stores as one tensor. Complete PTX memory
admission, general execution existence, hardware progress and whole-solver
instruction correspondence remain separate obligations. Documentation and saved
empirical evidence distinguish these from the completed phase-by-phase theorem.


A concurrent arithmetic extension now proves that actual final loads recover the
middle stores through the last barrier, using one source assignment for the whole
history. From one actual run, it derives the middle prefix, the state after the
last barrier and its continuation, then proves the final register's TorchLean
local cell value. A combined concurrent machine also executes the actual output
index/store/return tail while other threads continue. Its arithmetic run,
retained event positions and result-register relation are derived by proof;
padding lanes branch to the actual return without storing.

The memory proof also allows removing disjoint output stores from an interleaved
history while preserving the byte sources of its retained arithmetic reads.
Actual coefficient addresses are bounded, and the fetched output tail preserves
those bytes under the nonwrapping layout bounds. This supplies the memory
separation argument. The combined numerical theorem now derives actual
global-store addresses from launch registers and nonwrapping layout bounds.
Each completed active lane's stored bytes equal its TorchLean local cell result
in that same run. Distinct lane IDs and a common cell ID give disjoint output
words. Completed active lanes are proved to emit their stores. Publishing those
actual records in any order yields one row-major output tensor equal to the
TorchLean local cell calculation, independently of the old output bytes. This
mathematical publication does not prove CUDA host visibility or full PTX admission. A completed zero-data Q1 witness includes interleaved output
stores, all padding returns and the whole-history source constraints. It does
not establish general execution existence or whole-kernel correspondence.


The seven-instruction register prologue is also proved from its launch context.
It establishes arena and shared addresses, lane and cell IDs, an active-lane
flag, and row/column coordinates, preserving memory and unrelated registers.
Its instructions and declarations are bound to the emitted element entries.
The active gather now separately proves its four-byte connectivity load, indexed
eight-byte source load and shared store, with derived access bounds and preserved
setup registers. Its stored word agrees with TorchLean input gathering. A concurrent prefix theorem now derives the original input reads, each gathered
word, actual first-barrier completion and the arithmetic entry registers. Its actual gathered producers are connected to the body numerical theorem
through a common account of input read sources.

Actual gather-store records are also derived from that run: every active lane
writes, padding lanes do not, and each record has the proved source word at its
own disjoint shared slot. Real first-barrier arrivals and continuation slot preservation now establish
what later arithmetic reads see. The numerical theorem now uses a byte view derived from those producers,
with a proved change of source accounting. Its actual result and published
whole-cell tensor use TorchLean connectivity gathering and decoded coefficient
tables. The prefix input-source constraints are derived from the joint history:
setup/control and input addresses are established before admitting each load,
and the actual output stores are separated from the input arrays. The full-entry theorem derives the actual prefix and continuation from one
execution and transports the same byte-source constraints between their
instruction-counter views. No convenient shared bytes are installed in the execution.

The complete cell theorem names the operator whose coefficients were uploaded.
A representation contract relates each initial binary64 word of the B, D and W
tables to the corresponding TorchLean coefficient, and requires equal numbers
of quadrature points and interpolation nodes for this square-table kernel.
The proof preserves the ordered calculation when transporting tensor dimensions
and concludes equality with that operator's localAction. This is an input
representation contract, not an assumption about the computed output. External
host generation and serialization of those tables are not proved by it.

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

The cell-to-assembly theorem uses the operator's actual connectivity arrays.
A finite checker decodes ordered contribution rows from the uploaded integer
tables. Actual cell executions share one initial global memory; their stores
are confined to their own active output coordinates and preserve assembly
metadata. Publishing these histories and executing assembly produces the
TorchLean tensor operator with the same rounded addition order and optional
boundary mask. A nonzero complete-cell and assembly example checks the
connection without supplying expected intermediate values.

The grid extension interleaves actual cell instruction steps across blocks and
keeps each block's shared memory and barriers private. It derives the original
cell source contracts from the one tagged history and proves that chronological
publication preserves both cell results and assembly metadata. The next launch
then computes the same operator. Mathematical publication remains distinct from
CUDA visibility. Arbitrary-input cell-grid existence, GPU scheduling progress,
external serialization and remaining solver instructions remain explicit work.
The dot reductions now have the complete native-entry result described below.

The executable array reference and the tensor operator now have a proved
connection. The actual reference loops enumerate cells and local coordinates
in the same order and perform the same rounded updates. With valid finite input,
the public Poisson.apply function returns exactly the vector published by the
unmasked cell/assembly composition; no change to the reference computation or
its input validation is needed.

Supplied admitted cell executions with common entry arguments now construct an
actual grid schedule and its admitted sources. A serial block order is used
only to witness existence; the correctness theorem still covers arbitrary
admitted interleavings. Constructing the local cell runs for arbitrary inputs
remains separate. The nonzero cell/assembly regression checks both constructed
launches rather than assuming a grid execution.

The fresh-residual subtraction consumes actual cell/assembly publication.
Right-hand-side preservation follows from the preceding stores and disjoint
physical arrays. The resulting binary64 residual equals that original
right-hand side minus the rounded operator, with the same optional assembly
mask. A constructed nonzero example covers all three stages. This is separate
from exact-real residual certification, reduction order and solver stopping.

The in-place reductions require more visibility information than the cell's
single-writer arrays. A necessary repeated-write contract now excludes obsolete
and future sources using explicit coherence and causal order. The producer's
identity and read value follow byte by byte from actual history conditions,
with positive and negative fetched-execution regressions. This prepares the
memory argument; the emitted 256-thread reduction's ownership, ordering,
numerical computation and execution existence remain unproved.

The local tree-reduction update now has instruction-level rounded correctness,
execution existence and memory bounds, with source-text checks against the six
emitted dot kernels. This covers one active lane's pairwise update on a byte
view. The whole reduction still needs that view derived from actual concurrent
sources, the strided input accumulation and all tree stages composed in their
specified numerical order.

Reduction source selection now uses each word's owning lane and the shrinking
active ranges. Once store sites and active lanes are established, the own-word
and neighbor reads recover the intended previous write without presumed load
values. A completed four-lane example checks two real rounded update stages,
barriers and explicit byte sources, including rejection of an obsolete neighbor
value. The complete native-entry proofs below additionally derive the coverage
and control facts and compose the actual input loop, tree and output tail.

The 256-lane shared-tree fragment now derives every read's preceding
publication from actual lane guards, address arithmetic and barrier execution.
Its source-selection theorem covers arbitrary finite interleavings under the
explicit necessary byte-source rules. The standalone fragment uses combined lane-test
guards and supplied partial sums. The complete native-entry result below removes
those boundaries using actual predicates, input loops and the output epilogue. The numerical
composition and complete execution result below apply to this shared-tree
fragment.

The shared-tree fragment now has both numerical correctness and general
execution existence. Every completed admitted execution stores the prescribed
eight-round binary64 reduction of its 256 input words. Valid input storage
gives a constructed complete execution with admitted byte sources and all
barriers completed; every actual memory access stays within the shared
allocation. The universal result preserves permitted floating-point encodings
and operation order. The complete emitted dot-product entry now has the stronger result described
below; solver composition remains unfinished.

The reduction components now include separately scheduled native lane
comparisons and branches, with correctness and execution existence inherited
through a proved translation. A separate fetched proof establishes every lane's
strided input sum from actual global loads, the unsigned loop test and separate
rounded multiply/add operations, with arbitrary-input execution existence.
Frontend checks compare the entire native tree and input program with the
emitted code. Joining these components into one admitted concurrent entry,
including its final shared load and output store, remains part of complete
solver correspondence.

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

The complete program and its absolute branch targets are compared with emitted
PTX, including the conditional return, final shared load, output address
arithmetic and global store. Output-address ownership is proved independently
of the stored numerical value. The native numerical theorem now connects the
same input execution, shared tree, final shared read and actual output store.
A complete admitted native-entry execution witness is also constructed. The
full PCG launch sequence remains open.

The first shared publication is connected to that same thread's admitted
input traversal. A stronger projection tracks the recovered registers until
the actual store: only the two temporary address registers may change. The
shared base, lane number and accumulator therefore come from the executed
setup and input calculation. The two address instructions produce the lane's
own eight-byte slot. With a lane number below 256 and an aligned, nonwrapping
2048-byte shared allocation, the store is within bounds. Its decoded word is
that lane's ordered rounded partial sum; neither the word nor a shared-memory
snapshot is supplied as a premise.

Every returned thread has crossed all nine tree barriers, including a lane
taking the conditional return after the final barrier. Each crossing entails
an actual completion event with earlier arrivals from every thread at the
same resource, instruction site and barrier round. This follows from fetched
branch targets, return placement and the barrier state transitions. These
facts provide synchronization evidence for later reads; they do not by
themselves identify those reads' byte sources or numerical values.

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

The native dot-output theorem applies to every recorded global store in an
admitted execution, with 256 correctly numbered lanes, common initialized input
bytes, bounded input count, valid arrays, disjoint output storage and nonwrapping
addresses. It preserves the freedom of exceptional binary64 encodings by stating
decoded-value equality. A separate complete native-entry witness establishes
that the source-admitted execution and its output store exist. The remaining
PCG kernels and host launch composition are unfinished. Byte compatibility and ordered sources are explicit necessary
memory constraints, not a claim of full PTX admission or hardware conformance.

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

A returned lane-zero execution must contain the actual dot output store: its
computed predicate prevents the early return. Merging the actual global stores
in any order yields the prescribed decoded dot result at the output address and
preserves every other byte. This also holds for a constructed complete admitted
execution. The theorem concerns mathematical publication of complete recorded
stores. It does not assume atomic hardware reads, fix exceptional encodings,
or prove CUDA visibility or transport between hardware launches.

The search-direction update has a complete per-thread fetched proof. Each
active thread executes the real launch-parameter and index setup, loads scalar
β and its old p and z words, computes the separately rounded product β · p,
adds z, stores the result and returns. Every other byte remains unchanged.
Padding threads return without memory accesses. Valid allocations give finite
execution witnesses for both paths. The 25-instruction Lean program is compared
with the emitted update_p entry, including the product register, scalar address,
in-place output address and unsigned guard. The parallel proof derives old inputs from the same actual interleaved history
and publishes the separately rounded update. The full PCG loop remains separate.

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

The combined PCG update computes x := x + alpha*p, then r := r - alpha*ap,
then z := r/diagonal. Here ap is the already computed operator applied to the
search direction. At boundary coordinates the divisor is the exact binary64
word for one. Alpha is loaded once and reused; each multiplication, addition,
subtraction and division rounds separately. The preconditioner uses the newly
computed residual register. No real-number rearrangement or fused operation
replaces the emitted arithmetic.

The full 54-instruction fetched entry is proved, including launch indexing,
active and padding paths, all input loads, three stores and return. Its physical
layout bounds and aligns one scalar, six disjoint binary64 arrays and the
four-byte boundary flags. Output arrays x and r reuse their own initial storage.
Earlier stores preserve every later input field. Actual instruction addresses
and array ownership exclude stores by other threads; the x and r reads precede
their own writes. Byte compatibility and the explicit same-thread no-future
source rule therefore derive the old input words from initialization. The
boundary load is separately justified by four-byte source compatibility.

Every completed admitted active-coordinate interleaving publishes the three
rounded initial-input formulas and preserves every byte outside x, r and z.
A separate construction executes the same entry, preserves only not-yet-consumed
input words, and produces a finite joint history with compatible initial-byte
sources and the no-future constraint. Arbitrary input words, including exceptional
values and zero diagonals, are permitted; numerical acceptance remains separate.
The emitted entry is bound instruction for instruction across the saved layouts.
These are necessary fragment admission constraints, not the complete PTX memory
model. Joint padding scheduling, CUDA visibility, hardware conformance,
scalar decision kernels and full host PCG
composition remain separate obligations.

Restart copies the freshly recomputed residual into r and divides it by the
diagonal to obtain z and p. At boundary coordinates it substitutes the exact
binary64 word for one as divisor. The two quotient stores use the same actual
result word, including any permitted exceptional-value encoding. The residual
copy is bit for bit. These are statements about the actual loads, arithmetic
instruction and stores, not supplied numerical answers.

The complete 34-instruction fetched entry includes launch indexing, the active
and padding paths, the four-byte boundary load and return. A physical layout
bounds and aligns five mutually separate binary64 arrays and separate boundary
flags. Actual instruction addresses derive array ownership. No output store
can overlap a source-residual, diagonal or boundary read, so byte-source
compatibility forces every input read to the initial memory. Every completed
admitted active-coordinate interleaving publishes r, z and p with the stated
values and preserves bytes outside those output arrays. Independently, the
same instruction list has a finite joint execution with compatible initial-byte
sources for arbitrary input words; no nonzero-diagonal or finiteness assumption
is needed for execution. Numerical acceptance is a separate question.

The emitted restart entry is compared instruction for instruction across saved
layouts. The necessary fragment source constraints do not establish the complete
PTX memory model, and finite schedule existence does not establish GPU fairness.
Joint padding scheduling, CUDA visibility and hardware conformance remain
separate. Scalar decision kernels and host-loop composition
still need their corresponding results before claiming complete solver
correspondence.

Initialization reads each coordinate's load and boundary flag. It substitutes
positive zero for the load at boundary coordinates, copies that same word to
rhs and r, divides by the diagonal (substituting one on the boundary), and
stores the same actual quotient word to z and p. A separate immediate-word
store initializes x to positive zero. The predicate chosen from the boundary
flag survives the intervening stores and diagonal load; no desired predicate
outcome or numerical input is supplied to the proof.

The complete 43-instruction fetched entry includes actual launch indexing,
active and padding paths, word and four-byte loads, all five stores and return.
Its bounded, aligned physical layout separates seven binary64 arrays and the
boundary flags. In particular the early rhs/r stores cannot alter the later
diagonal load. Actual access classification and physical ownership show that
no output store can supply any input read. Word and four-byte source
compatibility therefore force the initial input bytes. Every completed admitted
active-coordinate interleaving publishes all five stated outputs and preserves
every byte outside rhs, r, z, p and x. Independently, a finite joint execution
with compatible sources exists for arbitrary input words. Zero diagonals and
exceptional values do not prevent execution; numerical acceptance is separate.

The exact emitted instruction list is bound across saved layouts, including
both zero-word instructions and the boundary divisor. These results use necessary
fragment admission constraints, not the complete PTX memory model. Joint padding
scheduling, GPU fairness, CUDA visibility and hardware conformance remain
separate. Scalar decision kernels and host-loop composition remain obligations
for full solver correspondence.
