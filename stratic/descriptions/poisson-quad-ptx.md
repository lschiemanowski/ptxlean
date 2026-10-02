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
external serialization, remaining reductions and solver instructions remain
explicit work.

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
