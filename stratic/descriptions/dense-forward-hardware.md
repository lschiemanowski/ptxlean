# Dense–ReLU forward on hardware

This validation runs y=ReLU(Wx+b) for finite binary32 inputs on an NVIDIA GPU.
One thread group computes each output row using the existing compact shared
memory reduction. The row width is a power of two at most 1024, with zero
padding for shorter input vectors. Empty output vectors require no launch;
empty input vectors return ReLU of the bias. Backward, softmax execution and
performance measurement are separate work.

The kernel body is emitted from the same Lean instruction list used by the
formal proof. A restricted emitter preserves instruction order, predicates,
explicit rounding, separate multiply and add operations, and barrier sites.
Body loads and stores are explicitly relaxed, with GPU scope for global memory
and thread-group scope for shared memory, matching the modeled access forms.
Unsupported forms are errors. A sidecar records each formal instruction and
its generated text. Kernel entry code supplies thread identity and a real
global-memory base; modeled addresses remain byte offsets and each actual
memory instruction adds the corresponding global or shared allocation base.
The entry code also zeroes every shared plane and synchronizes, matching the
formal initial shared array. The launcher supplies the exact group count, row
width and shared-memory extent.
These adaptations are reviewed and tested; there is no general verified PTX
compiler, runtime proof or hardware-refinement theorem.

Formal semantics stay pinned to PTX 9.4. Runnable artifacts declare their own
PTX version and GPU target. Using an older supported version requires an explicit
compatibility account for every emitted instruction form; the runner never
silently retries with a different version. Compiler rejection, resource limits
and CUDA failures are reported as such, not counted as numerical successes.

Identical input words feed the Lean arithmetic reference, GPU kernel, exact
rational mathematical reference and PyTorch. The Lean reference fixes the
proved balanced rounding order. On the finite supported domain, GPU words
must match that reference, including signed-zero behavior. Exact rational
arithmetic computes ReLU(Wx+b) without reference-rounding error, and separately
checks the finite intermediate range premises and the theorem's per-operation
rounding allowance. These executable checks are not newly proved Lean theorems.
The ordinary PyTorch computation uses pinned settings for full FP32 arithmetic;
its different reduction order is recorded, and its differences are reported
separately from the bound for our kernel. Its diagnostic allowance is
`(k*u*sumAbs+k*2^-150)/(1-k*u)`, with k=2*n+2, u=2^-24 and sumAbs the sum
of absolute real products and bias. This is a conservative test threshold,
not a proved bound for the concrete PyTorch backend. Exceeding it fails the run.
No backward activation margin is required for forward ReLU accuracy, including inputs near its corner.

Hand-chosen and reproducibly generated cases exercise padding, cancellation,
rounding ties, signed zero, small subnormal values, empty dimensions, and multiple
thread groups. Every case records whether the numerical premises hold. Source
regions and guard words surrounding allocations must be preserved. Repeated
launches and available memory, shared-memory race and synchronization checkers
provide additional empirical evidence, without establishing universal hardware
conformance or scheduler fairness.

Reports retain exact input and output bits, case seeds, source and artifact
hashes, formal reference identities, launch dimensions, compiler options and
versions, GPU and driver identity, PyTorch precision settings, observed errors,
range checks and sanitizer outcomes. The common runner and reporting format are
reusable; this component provides only the dense-forward adapter. A failed
comparison retains a reproducer and fails the run rather than enlarging a
tolerance or dropping the case.
