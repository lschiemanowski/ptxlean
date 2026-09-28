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
The existing formal instruction execution model does not yet cover this new
binary64 backend: generated text, compilation, launch and execution are tested,
not asserted to be a proved refinement of the Lean algorithm. Neither these
tests nor a small algebraic residual establish a continuous PDE error bound.

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

The numerical comparison uses fixed absolute and relative tolerances. A
converged result must satisfy the GPU's freshly measured residual tolerance.
Lean separately applies its operator to that result for an independent residual
comparison. That check allows an absolute 2e-12 measurement discrepancy when
corroborating convergence; it does not certify exact satisfaction of an
arbitrarily tighter tolerance in the independent arithmetic.
