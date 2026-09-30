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
registers. The final phase's entry registers are also explicit. The prologue and
gather must establish those inputs. The combined concurrent output tail still
needs general store-address bounds and final stored-tensor recovery. Complete PTX memory
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
separation argument. The combined numerical theorem still explicitly requires
the actual global stores' address bounds. Deriving these from launch registers
and recovering the stored output tensor from that same run remain open. A
completed zero-data Q1 witness includes interleaved output stores, all padding
returns and the whole-history source constraints. It does not establish general
execution existence or whole-kernel correspondence.
