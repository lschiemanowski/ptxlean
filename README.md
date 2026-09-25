# PTXLean

PTXLean is a Lean formalization of NVIDIA's PTX instruction language. It targets **PTX instruction set architecture (ISA) 9.4**. A central goal is allowing to prove that kernels written in PTX implement functions specified in e.g. TorchLean.

This is very early alpha. Full coverage of PTX is the eventual goal.

This project has been realized with GPT 6 Astra and Luna.

The code is accompanied by descriptions managed in [stratic](https://github.com/lschiemanowski/stratic). The current implementation covers selected instructions,
restricted memory and synchronization, and the forward/backward example below.

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
both kinds of evidence.

## Example: squared affine, forward and backward

The function takes three real scalars—an input `x`, a weight `w` and a bias
`b`—and returns one real scalar:

```text
F : ℝ × ℝ × ℝ → ℝ
A = x*w + b
F(x,w,b) = A²
```

TorchLean represents this computation as a graph and automatically constructs
its real-valued backward:

```text
backward : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
backward(x,w,b,upstream) = (dx,dw,db)
dx = 2*upstream*A*w     dw = 2*upstream*A*x     db = 2*upstream*A
```

`upstream` is the derivative arriving from the rest of a computation. If `F`
feeds a final loss `L`, pass `upstream = ∂L/∂F`; the backward returns
`(∂L/∂x, ∂L/∂w, ∂L/∂b)` by the chain rule. To compute the gradient of `F`
itself, pass **1**. The Lean definitions call this argument `d`. It is an input
to differentiation, not another parameter of the forward network. This interface
is called a vector–Jacobian product: it propagates output sensitivities back to
inputs and parameters, and also works when a network has several outputs.

The proofs concern **arbitrary inputs**, under the stated execution and numerical
conditions. TorchLean's generated backward computes the exact real derivatives.
The separately authored PTX implementation uses binary32 (32-bit single-precision)
operations; its proofs establish execution existence and bounds on the errors of
the stored forward result and gradients. They do not differentiate floating-point
rounding or assert bitwise equality with a PyTorch run.

### Forward PTX

The forward uses two serialized launches. The PTX below shows their instruction
bodies, with symbolic 64-bit address registers such as `%x` and `%A` supplied at
launch. `%r0` through `%r4` hold 32-bit words. The Lean programs construct these
instructions directly; register declarations, address setup and host launch
wrappers are not verified here. Each numbered launch is a **separate kernel**.
The output location `%y` initially contains positive zero.

```ptx
// Launch 1: store A = round(round(x*w) + b).
ld.relaxed.gpu.global.u32 %r0, [%x];
ld.relaxed.gpu.global.u32 %r1, [%w];
ld.relaxed.gpu.global.u32 %r2, [%b];
mul.rn.f32 %r3, %r0, %r1;
add.rn.f32 %r4, %r3, %r2;
st.relaxed.gpu.global.u32 [%A], %r4;
exit;

// Launch 2: store y = round(round(A*A) + 0).
ld.relaxed.gpu.global.u32 %r0, [%A];
ld.relaxed.gpu.global.u32 %r1, [%A];
ld.relaxed.gpu.global.u32 %r2, [%y];
mul.rn.f32 %r3, %r0, %r1;
add.rn.f32 %r4, %r3, %r2;
st.relaxed.gpu.global.u32 [%y], %r4;
exit;
```

### Backward PTX

The backward recomputes `A`, then computes `q = 2*upstream`, `db = q*A`,
`dx = db*w` and `dw = db*x` in five serialized launches. `%b_A` names the
initial bias slot, reused for `A` after its value has been loaded. `%two` and
`%zero` hold binary32 positive two and positive zero. `%upstream` points to the
incoming derivative. Register values are local to each launch; intermediate
results are passed through the displayed stores and loads.

```ptx
// Launch 1: recompute A, overwriting the bias slot.
ld.relaxed.gpu.global.u32 %r0, [%x];
ld.relaxed.gpu.global.u32 %r1, [%w];
ld.relaxed.gpu.global.u32 %r2, [%b_A];
mul.rn.f32 %r3, %r0, %r1;
add.rn.f32 %r4, %r3, %r2;
st.relaxed.gpu.global.u32 [%b_A], %r4;
exit;

// Launch 2: q = round(round(2*upstream) + 0).
ld.relaxed.gpu.global.u32 %r0, [%two];
ld.relaxed.gpu.global.u32 %r1, [%upstream];
ld.relaxed.gpu.global.u32 %r2, [%zero];
mul.rn.f32 %r3, %r0, %r1;
add.rn.f32 %r4, %r3, %r2;
st.relaxed.gpu.global.u32 [%q], %r4;
exit;

// Launch 3: db = round(round(q*A) + 0).
ld.relaxed.gpu.global.u32 %r0, [%q];
ld.relaxed.gpu.global.u32 %r1, [%b_A];
ld.relaxed.gpu.global.u32 %r2, [%zero];
mul.rn.f32 %r3, %r0, %r1;
add.rn.f32 %r4, %r3, %r2;
st.relaxed.gpu.global.u32 [%db], %r4;
exit;

// Launch 4: dx = round(round(db*w) + 0).
ld.relaxed.gpu.global.u32 %r0, [%db];
ld.relaxed.gpu.global.u32 %r1, [%w];
ld.relaxed.gpu.global.u32 %r2, [%zero];
mul.rn.f32 %r3, %r0, %r1;
add.rn.f32 %r4, %r3, %r2;
st.relaxed.gpu.global.u32 [%dx], %r4;
exit;

// Launch 5: dw = round(round(db*x) + 0).
ld.relaxed.gpu.global.u32 %r0, [%db];
ld.relaxed.gpu.global.u32 %r1, [%x];
ld.relaxed.gpu.global.u32 %r2, [%zero];
mul.rn.f32 %r3, %r0, %r1;
add.rn.f32 %r4, %r3, %r2;
st.relaxed.gpu.global.u32 [%dw], %r4;
exit;
```

Each multiply and add rounds separately to nearest, with ties to even. The zero
additions remain real instructions; the model does not replace these pairs with
fused multiply-add. The example uses one thread per launch, initialized aligned
storage, and completed, visible writes between launches without interference.
A real runtime must establish that serialization contract. Numerical error bounds
add finite-input, input-encoding error and overflow-range conditions; execution
existence applies even to bit patterns outside those numerical conditions.

The general forward accuracy theorem is `stored_forward_error` in
[PtxAffineSquareKernel.lean](integration/torchlean/PtxAffineSquareKernel.lean);
the backward theorem is `stored_backward_approximation` in
[PtxAffineBackward.lean](integration/torchlean/PtxAffineBackward.lean).
Both modules separately prove `pipeline_exists` and `pipeline_correct`.
The [forward walkthrough](docs/foundations/affine-square-kernel.md),
[automatic backward](docs/foundations/affine-square-vjp.md), and
[PTX backward walkthrough](docs/foundations/recomputed-affine-backward.md)
explain their hypotheses and connections.

## Run the checks and examples

The commands below check the formalized executions and their proofs. They do
not launch GPU kernels. The tested environment is Linux with Bash, Git, Python 3.11 or later,
`curl`, and [Elan](https://github.com/leanprover/elan), Lean's standard version
manager. Install Elan through its official instructions or
[release binaries](https://github.com/leanprover/elan/releases). Elan reads `lean-toolchain` and selects Lean **4.34.0**,
including its Lake build tool.

```sh
git clone https://github.com/lschiemanowski/ptxlean.git
cd ptxlean
python3 scripts/check_sources.py --fetch
./scripts/check.sh
cd integration/torchlean
lake exe cache get
./check.sh
```

The source command downloads NVIDIA’s manual as data into an ignored local cache
and verifies the exact reviewed hash; the manual is not distributed with this
project. The root check builds the dependency-free PTX core and checks its source,
proof and worker-evidence records. The integration commands fetch dependencies
at the commits in the committed `lake-manifest.json`, obtain compatible upstream
mathlib build artifacts, and check the TorchLean examples, numerical bounds and
forward/backward implementation proofs.

Successful runs end with `All source, build, and proof-dependency checks passed.`
and `Integration check passed: 363 exact dependency reports, only standard Lean
axioms.` respectively. The general forward and backward proofs above are included.

A smaller [array-loop example](docs/foundations/array-mask-select.md) combines
reviewed integer instructions with memory and branches, proving exact output,
memory safety and termination. After `lake build`, check it with
`lake env lean examples/array_mask_select.lean`.

## Instruction reference

The [HTML instruction reference](docs/instructions/index.html) lists every instruction
entry from the pinned PTX 9.4 inventory. Documented forms have original explanations,
explicit restrictions, and the associated Lean definitions and proofs. Reviewed
leaf forms are distinguished from restricted core models.

Open `docs/instructions/index.html` in a browser after cloning; no server or network
is needed. Rebuild with `python3 scripts/build_instruction_docs.py`, or verify that
the checked-in pages are current with `python3 scripts/build_instruction_docs.py --check`.

## Sources and license

The [source ledger](docs/foundations/source-ledger.md) records interpretation of
the pinned NVIDIA PTX 9.4 documentation separately from checked proofs.
Project code is distributed under [Apache-2.0](LICENSE). NVIDIA documentation is
obtained separately from NVIDIA; upstream dependencies retain their own licenses.
