# TorchLean and PTX integration

This separate Lean package uses real upstream TorchLean at the revision pinned in
`lakefile.toml`; `lake-manifest.json` fixes its transitive dependencies. Its Lean
4.34 toolchain matches the root PTX project. A local path dependency imports the
actual root `ptxlean` package alongside TorchLean in the same Lean build.

The introductory [ReLU-neuron example](../../docs/foundations/relu-neuron.md)
computes `max(w*x+b,0)`. `PtxReluVJP.lean` proves the actual generated backward,
including its zero convention and derivative interpretation away from zero.
`PtxReluKernel.lean` supplies separately authored forward and recomputing backward
executions; `PtxReluAccuracy.lean` connects their stored results to TorchLean.
The numerical backward theorem requires an explicit margin preventing rounding
from changing the activation branch. The finite bit gate is implemented in
`PtxBinary32/Relu.lean` and `PtxBinary32/ReluGate.lean` using existing instructions.

## Retained squared-affine graph

The original example computes `(x * weight + bias)^2` independently at each coordinate of
an arbitrary tensor shape. It is a diagonal affine map followed by squaring, not
a dense matrix layer. All three tensors are variable inputs, so the generated
backward computation includes weight and bias sensitivities. The seed is an
arbitrary output-shaped tensor. No backward formula is implemented here:
TorchLean composes the existing primitive reverse rules.

`PtxTorchLean.lean` contains:

- `affineSquare`: an upstream `DGraph` built from multiplication, addition and
  square nodes, with upstream local derivative certificates.
- `forward_polynomial`: the selected graph forward value at every coordinate
  equals `(x_i * weight_i + bias_i)^2`, independently of the VJP theorem.
- `checked_success`: the actual checked graph interface returns `.ok` for every
  real-valued input and seed. The proof discharges this graph's validation rather
  than assuming execution succeeded.
- `checked_success_vjp`: the returned backward values equal the mathematical VJP
  of the selected graph output. The auxiliary `checked_vjp` exposes the general
  upstream success premise; `checked_success_vjp` discharges it.
- `unsigned_min_scalar_embedding`: a narrow theorem using both libraries. The
  natural-number value of modeled PTX unsigned minimum embeds into a real scalar
  tensor. This does not prove any kernel implements the network graph.
- `exact_tape_success_vjp`: success and the derivative correspondence for the
  lower-level exact tape, including its saved intermediate values.

The backward example contains proofs over exact real values. They do not make real numbers executable
hardware values, certify floating-point error, or prove a PTX implementation.
The mathematical VJP endpoint differentiates the actual graph forward map;
`forward_polynomial` establishes its correspondence to the displayed polynomial.
The current graph has no state updates, masks, parameter sharing or nonsmooth
operations. General model lowering and network-scale numerical/kernel correspondence remain open.
The serialized scalar forward bridge below establishes one restricted numerical
correspondence for this actual graph.

## Global-memory integer tensor bridge

`PtxTensorBridge.lean` connects the existing five-instruction vector-add program
to actual TorchLean tensors. Its input is a supplied word allocation and arbitrary
initial register files, using the interleaved layout `[left, right, output]` for
each coordinate. It proves addition modulo `2^32`, finite instruction execution,
access safety, unchanged words outside outputs, and a valid relational memory
witness with matching execution labels. A separate input-only no-overflow
condition gives exact real-tensor addition for the unsigned integers embedded
into the reals. This is not a floating-point interpretation.

The [study guide](../../docs/foundations/tensor-layout-bridge.md) explains the
layout, the direct overflow execution example, the bounds excluding missing-cell
defaults, and the restricted memory-candidate family. The theorem audit contains
all 15 bridge declarations. Their exact source snapshot is recorded separately
in `verification-tensor-bridge.json` and `proof-audit-tensor-bridge.txt`.

## Encoded single-precision arithmetic

The [binary32 guide](../../docs/foundations/binary32.md) explains the exact bit
adapter, nearest-even addition and multiplication, and the conservative envelope
for unspecified NaN results. Signed zero and subnormal values are preserved;
exceptional encodings have no finite real interpretation. The
[range proofs](../../docs/foundations/binary32-ranges.md) derive finite results
from input bounds. The [composition proofs](../../docs/foundations/binary32-error-composition.md)
carry incoming errors through addition, multiplication and a separately rounded
multiply-then-add expression. The reviewed `PtxBinary32/Instructions.lean`
connects the numerical relations to fetched, predicated instruction occurrences.
`Mixed.lean` and `Affine.lean` connect actual global-memory loads and stores to
those instructions; the [walkthrough](../../docs/foundations/mixed-affine.md)
states their target, typing and memory restrictions. The NaN envelope does not establish
that every included NaN encoding can occur on hardware.

## Two serialized kernels and the same graph's generated backward

`PtxAffineSquareKernel.lean` reuses the actual affine instruction program twice.
The first launch stores x*weight+bias; the second loads that same stored word
twice and squares it, with an explicit zero addition. `PtxBinary32/Sequential.lean`
checks live logical allocation identities and device ownership, assembles each
launch from its own supplied registers and arguments, and writes back the actual
completed run's memory. The root storage module proves permanent invalidation
after release, including after later reservations and writes.

The [two-kernel guide](../../docs/foundations/affine-square-kernel.md) follows
both traces, the existence proof for arbitrary input bits, and the final stored
output's error relative to the actual TorchLean graph. Its conditions constrain
initial inputs, not desired intermediate/output values. A real runtime must
establish completion, visibility and absence of interference between launches.
The proof does not derive these obligations from a PTX thread's exit.

`PtxAffineSquareVJP.lean` separately expands the upstream graph's actual generated
backward result for arbitrary real scalar inputs and an arbitrary output weight.
It proves checked success, the three explicit sensitivities, and mathematical
derivative correspondence. The [backward guide](../../docs/foundations/affine-square-vjp.md)
explains this exact-real result. These exact-real proofs remain distinct from the independently authored
backward implementation below.

## Separately authored recomputing backward

`PtxAffineBackward.lean` selects five actual affine-program launches by hand.
The first recomputes the affine value in the bias slot after reading it. Four
more stages scale the incoming output weight and produce bias, input and weight
sensitivities. The [walkthrough](../../docs/foundations/recomputed-affine-backward.md)
shows the exact layout, request sequence and checked (84,56,28) example.

`PtxBinary32/BackwardPipeline.lean` proves the four-stage execution, trace, safety,
frame and all-bit existence contracts. `BackwardError.lean` retains every rounding
and propagates seed, operand and saved-value errors. The final stored-gradient
theorem derives the saved value and its error from the actual recomputation,
then uses `PtxGradientView.lean` to compare the actual stored words with TorchLean's
actual generated VJP. No desired output, correct saved value or successful AD
call is assumed. The observation interface rejects nonfinite encodings and
explicitly distinguishes same real value from same bits.

This is one scalar implementation under the serialized runtime contract, not an
automatic backward-code generator or a general network/PTX lowering result.
Its separately checked numerical and execution proofs do not certify host/runtime
visibility, physical ABI, hardware conformance or bitwise PyTorch agreement.

## Reproduce

From this directory in a fresh checkout, with Git, Bash, Python 3.11 or later,
`curl` and [Elan](https://github.com/leanprover/elan) available:

```sh
lake exe cache get
./check.sh
```

Elan selects the Lean 4.34.0 toolchain recorded in `lean-toolchain`. Lake obtains
the exact dependency commits recorded in the committed manifest. The first
command downloads compatible upstream mathlib build artifacts; it is the
standard mathlib cache command, not a project installer. Do not run `lake update`
to reproduce the release. To compile dependencies from source instead, use
`lake --no-cache build` in place of the cache command in a fresh checkout.

The checker itself requires the toolchain and dependency checkouts to be present;
it does not update pins, clone missing dependencies or request downloaded build
caches. It builds and checks the examples and their proofs, rather than running
GPU kernels. The root check, `./scripts/check.sh` from the repository root, should
also be run; the root README gives the complete command sequence.

It checks every manifest Git dependency's actual HEAD and rejects tracked file
modifications before and after verification. The root PTX package remains an
explicit local path dependency, whose separate root checks should also be run.
All 22 declared default targets are built with `lake --no-cache build`.
A fresh elaboration of `PtxIntegrationAudit.lean` must then produce exactly 439
distinct dependency reports, covering the graph, tensor bridge, numerical
adapters, instruction and execution layers, serialized launches, two-kernel
forward bridge, scalar generated backward and independently authored backward
implementation with a stored-gradient observation interface. `check.py` fixes the endpoint
counts by namespace, and the audit driver lists every name, including the ReLU
graph, finite gate, execution and numerical endpoints. Only the three
standard Lean axioms listed below are permitted.

The same command scans this package's own Lean sources, including its audit
drivers, for proof placeholders, new unchecked axioms, and `native_decide`.
Comments and string contents are excluded using the root proof checker's lexical
helper; upstream library sources are not scanned. Imported logical dependencies
are checked transitively by Lean's reports. The command also rejects changes to
the checked integration sources, root PTX Lean sources, pin/configuration files,
and checker helpers during the run. It also verifies the actual Lean version against the toolchain
pin. These checks establish source hygiene and proof dependencies,
not fidelity to PTX documentation, compiler behavior, or hardware. Check output
is written to the terminal and can be redirected to a caller-chosen log.

CUDA and LibTorch options are disabled. The focused theorem target avoids the
upstream umbrella library and native executables. Upstream dependencies still
include FloatLib proofs and documentation-package sources. The first completed
build used about 8.9 GB in `.lake`, plus a 2.9 GB Lean toolchain; downloaded mathlib
cache files also occupy the shared user cache.

The build prints the transitive logical dependencies of the graph and its public
endpoints. The verified endpoints use only `propext`, `Classical.choice` and
`Quot.sound`; no `sorryAx` or custom axioms occur in those reports. Logical proofs
do not certify upstream native/executable replacements. The paths claimed here
are the proof-visible exact semantics, not compiled numerical execution.

## Verification history

`verification.json` and `proof-audit.txt` preserve the initial isolated TorchLean
experiment. They identify earlier source hashes and are historical receipts.
The joint build is recorded separately in `verification-joint.json` and
`proof-audit-joint.txt`, including the root PTX source snapshot used in that build.
Neither receipt is a substitute for rerunning checks after changing its inputs.
