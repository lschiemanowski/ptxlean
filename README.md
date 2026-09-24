# PTXLean

PTXLean is an early Lean formalization of NVIDIA's PTX instruction language,
with reusable foundations for proving that GPU kernels implement neural-network
computations. It targets **PTX instruction set architecture (ISA) 9.4**. Full coverage is a goal;
the current release contains checked, explicitly restricted fragments and small
end-to-end examples.

## The idea

PTX is the low-level virtual instruction language used by NVIDIA GPU programs.
Instructions manipulate registers and memory, while many threads communicate
through shared storage and synchronization. A formal model must describe which
executions are permitted, including cases where more than one result is allowed.

The project connects three layers:

1. A mathematical computation over real numbers, specified in
   [TorchLean](https://github.com/lean-dojo/TorchLean).
2. Numerical operations on actual floating-point encodings, with explicit
   rounding and error bounds relative to that mathematical computation.
3. PTX instruction execution, including the values actually loaded and stored,
   memory ordering, and the conditions needed for execution to complete.

Lean checks the proofs connecting these layers. Whether the definitions faithfully
represent NVIDIA's specification is a separate question, addressed through pinned
source passages, semantic review and distinguishing examples. The project records
both kinds of evidence; a successful build alone does not establish PTX fidelity.

## Current status

The checked foundations include scalar integer execution, selected single-precision
floating-point operations, memory observations and ordering, message passing,
shared-memory barriers, and logical storage passed between serialized kernel
launches. A [shared-memory integer reduction](docs/foundations/shared-reduction.md)
combines computed addresses, a barrier and a summation loop, with proofs of output
correctness, final storage, execution existence and access safety.

The numerical example below connects actual modeled forward and backward
instruction executions to the same TorchLean graph. The current checks audit
**1,213 declarations in the core and 363 in the TorchLean integration**. Their
transitive logical dependencies contain only Lean's standard `propext`,
`Classical.choice` and `Quot.sound` axioms. Proof placeholders, new unchecked
axioms and `native_decide` are rejected in project sources.

This is a research foundation, with substantial work remaining: full ISA and
computing-model coverage, general neural-network lowering, asynchronous operations,
and large-model verification. The present results do not establish NVIDIA hardware
conformance, general GPU scheduling progress, or bitwise agreement with PyTorch.
Each fragment states its own execution and numerical restrictions. The
[Stratic descriptions](stratic/descriptions/root.md) explain those contracts;
[study guides](docs/foundations/guide.md) provide longer walkthroughs.

## Expanding the ISA with Luna

The intended route to full coverage is model-assisted instruction formalization
on top of shared, reviewed foundations. The current worker is **GPT-6 Luna**, run
through Codex headless. Routine instruction families are delegated; shared memory,
execution and numerical foundations are developed and reviewed separately.

For each bounded task, the workflow:

1. Pins the repository, PTX source passages, allowed edits, Lean interfaces and
   required theorem statements before generation.
2. Runs the worker in a separate checkout and retains its patch, logs, failures
   and repair feedback.
3. Replays the patch in a fresh checkout, builds it with the pinned toolchain,
   audits proof dependencies and checks independently prepared examples.
4. Separately reviews the definition against PTX's documented semantics, then
   integrates accepted changes and reruns the combined checks.

The [selected-form ledger](docs/formalization/implemented-forms.md) currently
records nine accepted forms: `min.u32`, `max.u32`, `clz.b32`, `popc.b32`,
`add.rn.f32`, `mul.rn.f32`, `selp.b32`, `min.s32` and `max.s32`. This is the
delegated-trial ledger, not a count of everything implemented in the project.
The five tasks needed 14 headless calls, including failures and repairs, with
substantial coordinator guidance. They demonstrate bounded capability, not an
established full-ISA success rate or cost estimate.

A **future independent inexpensive-model reviewer** will check candidates
against the source obligations and look for semantic mistakes. That automated
review stage is not implemented in this release. It will supplement Lean checks
and independently prepared tests; agreement between two models will not by itself
justify acceptance. Existing [mutation probes](stratic/descriptions/worker-review-probes.md)
exercise whether the acceptance checks reject deliberately incorrect candidates.

See the [worker guide](docs/formalization/worker-runs.md) and
[pinned provisioning workflow](docs/formalization/worker-provisioning.md).
Rechecking the released proofs and saved evidence requires no model access.

## Example: squared affine, forward and backward

Consider the scalar computation

```text
A = x*w + b
F(x,w,b) = A²
```

TorchLean represents this computation as a graph and automatically constructs
its real-valued backward. For an incoming output weight `d`, the backward returns

```text
dx = 2*d*A*w     dw = 2*d*A*x     db = 2*d*A
```

This is a vector–Jacobian product: `d` weights the output's sensitivity before it
is propagated to the inputs and parameters. The proofs establish that the actual
generated backward succeeds and computes these mathematical derivatives. The
TorchLean graph also supports coordinatewise tensors; the PTX example here is scalar.

The forward implementation uses two serialized kernel launches: one computes
and stores `A`, and the next reads and squares it. A separately supplied backward
implementation uses five launches: recompute `A`, scale `d`, then compute `db`,
`dx` and `dw`. Its instructions and correctness proofs are supplied separately
from TorchLean's automatic backward construction.

Each launch executes loads, a rounded binary32 multiply, a rounded binary32 add,
a store and an exit. Binary32 is the usual 32-bit single-precision format.
Multiplication and addition round separately to nearest, with ties to even;
the model does not silently replace them with fused multiply-add. The proofs
follow the stored bit patterns between launches, establish execution existence,
and bound the final numerical errors under explicit input and range conditions.

Concrete checked instances include:

| Example | Inputs | Stored result |
| --- | --- | --- |
| Forward | `x=1.5, w=2, b=0.25` | `A=3.25`, then `F=10.5625` |
| Backward | `x=2, w=3, b=1, d=2` | `(dx,dw,db)=(84,56,28)` |

These examples use initialized, aligned storage and one thread per launch.
The serialized runtime contract requires completed, visible writes between
launches and no interference. Proving this contract for a real host runtime,
compiler or GPU is outside the example. An error bound relative to real-number
derivatives is also distinct from bitwise equality with a PyTorch run.

The [forward walkthrough](docs/foundations/affine-square-kernel.md),
[automatic backward](docs/foundations/affine-square-vjp.md), and
[separately authored PTX backward](docs/foundations/recomputed-affine-backward.md)
explain the proofs. The concrete Lean theorems are `two_launch_example` in
[PtxAffineSquareKernel.lean](integration/torchlean/PtxAffineSquareKernel.lean) and
`five_launch_example` in
[PtxAffineBackward.lean](integration/torchlean/PtxAffineBackward.lean).

## Run the checks and examples

The commands below check the formalized executions and their proofs. They do
not launch GPU kernels. **No GPU, CUDA, LibTorch, Stratic or model account is
required.** The tested environment is Linux with Bash, Git, Python 3.11 or later,
`curl`, and [Elan](https://github.com/leanprover/elan), Lean's standard version
manager. Install Elan through its official instructions or
[release binaries](https://github.com/leanprover/elan/releases); there is no
PTXLean installer. Elan reads `lean-toolchain` and selects Lean **4.34.0**,
including its Lake build tool.

```sh
git clone https://github.com/lschiemanowski/ptxlean.git
cd ptxlean
./scripts/check.sh
cd integration/torchlean
lake exe cache get
./check.sh
```

The root check builds the dependency-free PTX core and checks its source,
proof and worker-evidence records. The integration commands fetch dependencies
at the commits in the committed `lake-manifest.json`, obtain compatible upstream
mathlib build artifacts, and check the TorchLean examples, numerical bounds and
forward/backward implementation proofs. No `lake update` is needed.

Successful runs end with `All source, build, and proof-dependency checks passed.`
and `Integration check passed: 363 exact dependency reports, only standard Lean
axioms.` respectively. Both concrete examples above are included. To re-elaborate
their files explicitly after setup:

```sh
lake env lean PtxAffineSquareKernel.lean
lake env lean PtxAffineBackward.lean
```

The integration is a substantial mathematical build: the tested dependency/build
directory occupied about 9 GB, plus roughly 3 GB for the Lean toolchain and
space for downloaded caches. The cache
command uses upstream precompiled dependencies; the project proofs are built
locally. To build dependencies from source instead, use `lake --no-cache build`
in place of `lake exe cache get` in a fresh checkout. The checker validates pinned
dependency revisions and rejects tracked dependency edits before and after the
build. See the [integration README](integration/torchlean/README.md#reproduce)
for details and the precise trust boundary.

## Sources and license

The [source ledger](docs/foundations/source-ledger.md) records interpretation of
the pinned NVIDIA PTX 9.4 documentation separately from checked proofs.
Project code is distributed under [Apache-2.0](LICENSE). Bundled NVIDIA reference
documentation retains its own notices; upstream dependencies retain their own
licenses.
