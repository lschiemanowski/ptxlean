# TorchLean and PTX integration

This separate Lean package uses real upstream TorchLean at the revision pinned in
`lakefile.toml`; `lake-manifest.json` fixes its transitive dependencies. Its Lean
4.34 toolchain matches the root PTX project. A local path dependency imports the
actual root `ptxlean` package alongside TorchLean in the same Lean build.

The example computes `(x * weight + bias)^2` independently at each coordinate of
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
operations. General model lowering and floating-point numerical/kernel correspondence remain open.

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
multiply-then-add expression. These numerical foundations do not yet fetch or
execute floating-point PTX instructions. The NaN envelope does not establish
that every included NaN encoding can occur on hardware.

## Reproduce

From this directory:

```sh
./check.sh
```

The checker requires Python 3.11 or later, Git, Elan with the pinned Lean 4.34
toolchain already installed, and the dependency checkouts recorded in the
committed manifest. It does not update pins, clone missing dependencies, or
request downloaded build caches. Provision the pinned dependencies and, if
desired, their compatible mathlib cache before running it; do not use
`lake update` merely to reproduce a build.

It checks every manifest Git dependency's actual HEAD and rejects tracked file
modifications before and after verification. The root PTX package remains an
explicit local path dependency, whose separate root checks should also be run.
All six registered integration targets are built with `lake --no-cache build`.
A fresh elaboration of `PtxIntegrationAudit.lean` must then produce exactly 85
distinct dependency reports: seven graph endpoints (including the graph
definition), 15 tensor bridge theorems, 16 binary32 core theorems, 16 encoded
examples, 12 input-bound theorems, ten error-composition theorems, and nine
binary32 adapter/reference definitions. Only the three standard Lean axioms listed below are permitted.

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
