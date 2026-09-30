# What is proved about the Poisson result?

The GPU solver proposes a solution. A separate Lean checker accepts it only if
its **exact discrete residual** meets the requested tolerance. This is called an
*a posteriori* certificate: it checks the result after computation, regardless
of how the solver obtained it. It is now a required step in
[`validate_poisson.py`](../../hardware/validate_poisson.py).

## The statement

Let `x` be the returned binary64 solution, `b` the saved load vector, and `A` the
assembled tensor operator defined by the saved basis, derivative, integration
weight and connectivity arrays. Interpret every finite binary64 word as the
exact rational number it represents. Acceptance implies:

- Every boundary value of `x` is exactly zero.
- On the interior nodes, `‖b − A x‖₂ ≤ max(atol, rtol · ‖b‖₂)`.

The norm is the ordinary Euclidean norm: the square root of the sum of squared
coordinates. The executable checker uses the equivalent inequality between
squared rational quantities. There is no floating-point residual calculation,
rounded square root or extra empirical tolerance in this check. The effect of
all rounding in the solver is captured in the actual stored `x` being checked.

These are the **represented discrete equations**: the rounded setup tables
transferred to the GPU define `A` and `b`. The theorem does not identify them
with ideal unrounded quadrature, nor bound their error relative to the
continuous Poisson equation. It also does not bound solution error from the
residual without a separate estimate of the inverse operator.

## Following the proof

1. [`PoissonQuadCorrespondence.lean`](../../integration/torchlean/PoissonQuadCorrespondence.lean)
   defines ordered contractions and the five local calculation phases.
   `cell_float_correspondence` connects them to the existing TorchLean
   `localAction` using Lean's logical binary64 model. `scatter_gather` shows
   that collecting contributions separately for each node preserves their
   accumulation order. No associativity of rounded addition is assumed.
2. [`PoissonResidualCertificate.lean`](../../integration/torchlean/PoissonResidualCertificate.lean)
   instantiates the actual TorchLean tensor expression with exact rationals.
   `computedApply_get` relates efficient vector assembly to its functional
   specification. `check_sound` recovers the exact acceptance conditions;
   `certified_residual` proves the real-valued Euclidean norm inequality above.
3. [`PoissonResidualInput.lean`](../../integration/torchlean/PoissonResidualInput.lean)
   decodes binary64 words using FloatLib. `decodeWord_real` connects that
   decoding to FloatLib's real interpretation. Parsing checks dimensions,
   array lengths, Q1–Q4 degree and uniform-square connectivity; it constructs
   the boundary from those dimensions. NaNs and infinities are rejected.
   `acceptedRequest_sound` connects accepted serialized input to the theorem.
4. [`PoissonResidualChecks.lean`](../../integration/torchlean/PoissonResidualChecks.lean)
   includes a closed acceptance proof for the recorded `n=2`, Q1 GPU solution,
   a rejection proof for an incorrect solution, and finite/exceptional decoding
   checks. These proofs use Lean kernel reduction, not `native_decide`.

The general theorem covers every accepted input. The integration audit checks
all public definitions and theorems for unexpected axioms; only the standard
Lean axioms `propext`, `Classical.choice` and `Quot.sound` are permitted. There
are no `sorry` proofs or new unchecked axioms.

## Why the CPU and GPU iterates may differ

The CPU dot product accumulates sequentially; the GPU partitions entries among
256 lanes and combines their partial sums in a tree. Rounded addition depends
on order. [`PoissonBinary64.lean`](../../integration/torchlean/PoissonBinary64.lean)
contains a kernel-checked example: the sequential sum of `[2^53, 1, -2^53, 1]`
is `1`, while the GPU-shaped tree produces `2`. Universal bitwise equality of
PCG iterates would therefore be the wrong contract. Both solutions can instead
be checked against the same equations and requested tolerance.

## Run the check

After installing the [pinned integration dependencies](../../integration/torchlean/README.md),
from the repository root:

```sh
# Fresh GPU execution, including mandatory exact certification:
python3 hardware/validate_poisson.py \
  --output .hardware-runs/poisson-local --ptx-version 9.2

# Certify an existing saved numerical run; no GPU or Torch needed:
python3 hardware/certify_poisson.py \
  --run .hardware-runs/poisson-local \
  --output .hardware-runs/poisson-recertified

# Check the general proofs, closed examples and dependency audit:
integration/torchlean/check.sh
```

Output directories must be new. Certification verifies saved artifact hashes,
rebuilds the pinned Lean checker, audits the main proof dependencies and records
exact residual/threshold fractions. It rejects modified boundary/interior
solutions, nonfinite weights, malformed shapes and altered connectivity in
negative controls. Iteration-limit and breakdown results are recorded as
uncertified, rather than treated as successful solutions.

## What remains outside this proof

This is **accepted-result correspondence**, not a proof that the PTX solver
always terminates, converges, or returns an acceptable vector. The [residual instruction proofs](poisson-instructions.md) connect the complete
`true_residual` entry to TorchLean subtraction, including its guard and byte
addresses. A parallel theorem recovers the whole output tensor from necessary
byte-source constraints and disjoint stores, without assuming sequential reads. The three middle cell phases also have instruction-level numerical correspondence;
a [final-body proof](poisson-final-output.md) extends it through a constructed
byte snapshot to the stored local cell result. A [concurrent extension](poisson-final-consumers.md)
now also justifies actual final arithmetic loads and connects its result state
to a [combined concurrent output tail](poisson-concurrent-output.md). General
output-store bounds and stored-tensor recovery, gather, complete memory
admission, remaining kernels and host
launch composition still require their instruction-level connections. Bounds on scalar array indices alone are not a full memory-safety
proof. GPU tests and the existing sanitizer evidence remain separate.

For the full numerical suite, running the compiled checker additionally trusts
Lean's compiler/runtime, the Python extraction of saved GPU words and the
input/output transport. Source and artifact hashes make this boundary
inspectable; they are not hardware-conformance proofs. The small recorded
acceptance instance is checked directly by Lean's kernel, so it does not rely
on compiled evaluation to establish that particular rational inequality.
