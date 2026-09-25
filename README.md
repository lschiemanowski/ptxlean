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

## Example: a ReLU neuron and its backward

A single neuron multiplies its input by a trainable weight, adds a trainable bias,
and applies ReLU, which replaces negative values with zero:

```text
F : ℝ × ℝ × ℝ → ℝ
A = w*x + b
F(x,w,b) = ReLU(A) = max(A, 0)

backward : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
backward(x,w,b,upstream) = (dx,dw,db)
g = upstream if A > 0, otherwise 0
dx = g*w     dw = g*x     db = g
```

`upstream` is the gradient arriving from the rest of the network. If `F` feeds a
loss `L`, it is `∂L/∂F`, and the backward returns `(∂L/∂x, ∂L/∂w, ∂L/∂b)`.
Use **1** to obtain the gradient of `F` itself. The Lean definitions call this
argument `d`; it is a backward input, not another trainable parameter.

TorchLean automatically constructs this backward from its multiplication,
addition and ReLU nodes. Its checked backward succeeds for every real input and
uses the convention **zero gradient at `A = 0`**. ReLU has no ordinary derivative
there: the mathematical derivative theorem requires **`A ≠ 0`**. These are general
results, not tests at a few selected numbers.

The separately authored PTX kernels use binary32 (32-bit single precision).
Multiplication and addition round separately to nearest, with ties to even.
The forward error bound applies on either side of zero and across the kink.
The backward error bound additionally requires the affine error budget to be
smaller than `|A|`, so rounding cannot change the activation decision. Finite
input values, input encoding errors and overflow-range conditions are explicit.
These proofs do not differentiate floating-point rounding or claim bitwise
agreement with a PyTorch run.

### Forward PTX

The following are the actual instruction bodies of **two separate launches**.
Symbolic address registers such as `%x` are supplied at launch; `%r0`–`%r4` hold
32-bit words. Register declarations, address setup and host launch wrappers are
outside the verified example.

The ReLU gate uses existing integer comparisons on binary32 encodings: zero has
all bits clear, and the high bit marks a negative value. For finite values, this
implements ReLU exactly, including returning positive zero for negative zero.
It is a small reference implementation, not an optimized kernel.

```ptx
// Launch 1: A = round(round(w*x) + b).
ld.relaxed.gpu.global.u32 %r0, [%w];
ld.relaxed.gpu.global.u32 %r1, [%x];
ld.relaxed.gpu.global.u32 %r2, [%b];
mul.rn.f32 %r3, %r0, %r1;
add.rn.f32 %r4, %r3, %r2;
st.relaxed.gpu.global.u32 [%A], %r4;
exit;

// Launch 2: y = ReLU(A).
ld.relaxed.gpu.global.u32 %r0, [%A];
ld.relaxed.gpu.global.u32 %r1, [%A];
setp.eq.u32 %p0, %r0, 0;
@%p0 mov.b32 %r1, 0;
setp.ge.u32 %p0, %r0, 0x80000000;
@%p0 mov.b32 %r1, 0;
st.relaxed.gpu.global.u32 [%y], %r1;
exit;
```

### Backward PTX

The backward recomputes `A` from `x,w,b`, gates the incoming gradient, and computes
the input and weight gradients. It uses **four separate launches** and does not
reuse a cached forward value. `%zero` holds positive zero; every displayed zero
addition is part of the implementation and its proof.

```ptx
// Launch 1: recompute A = round(round(w*x) + b).
ld.relaxed.gpu.global.u32 %r0, [%w];
ld.relaxed.gpu.global.u32 %r1, [%x];
ld.relaxed.gpu.global.u32 %r2, [%b];
mul.rn.f32 %r3, %r0, %r1;
add.rn.f32 %r4, %r3, %r2;
st.relaxed.gpu.global.u32 [%A], %r4;
exit;

// Launch 2: db = upstream if A > 0, otherwise 0.
ld.relaxed.gpu.global.u32 %r0, [%A];
ld.relaxed.gpu.global.u32 %r1, [%upstream];
setp.eq.u32 %p0, %r0, 0;
@%p0 mov.b32 %r1, 0;
setp.ge.u32 %p0, %r0, 0x80000000;
@%p0 mov.b32 %r1, 0;
st.relaxed.gpu.global.u32 [%db], %r1;
exit;

// Launch 3: dx = round(round(db*w) + 0).
ld.relaxed.gpu.global.u32 %r0, [%db];
ld.relaxed.gpu.global.u32 %r1, [%w];
ld.relaxed.gpu.global.u32 %r2, [%zero];
mul.rn.f32 %r3, %r0, %r1;
add.rn.f32 %r4, %r3, %r2;
st.relaxed.gpu.global.u32 [%dx], %r4;
exit;

// Launch 4: dw = round(round(db*x) + 0).
ld.relaxed.gpu.global.u32 %r0, [%db];
ld.relaxed.gpu.global.u32 %r1, [%x];
ld.relaxed.gpu.global.u32 %r2, [%zero];
mul.rn.f32 %r3, %r0, %r1;
add.rn.f32 %r4, %r3, %r2;
st.relaxed.gpu.global.u32 [%dw], %r4;
exit;
```

The execution model uses one thread per launch and initialized, aligned storage.
Launches complete with visible writes and no interference before the next begins;
a real runtime must establish that contract. Execution existence covers arbitrary
initial bit patterns, while the ReLU and numerical interpretations require finite
values. No claim about floating-point ReLU's NaN policy is made by this bit gate.

[PtxReluVJP.lean](integration/torchlean/PtxReluVJP.lean) proves the generated backward
and its mathematical meaning. [PtxReluKernel.lean](integration/torchlean/PtxReluKernel.lean)
proves execution existence and correspondence; [PtxReluAccuracy.lean](integration/torchlean/PtxReluAccuracy.lean)
connects the stored forward result and gradients to TorchLean with error bounds.
The [study guide](docs/foundations/relu-neuron.md) explains the proof conditions.
The earlier [squared-affine example](docs/foundations/affine-square-kernel.md) remains
in the verification suite.

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
and `Integration check passed: 439 exact dependency reports, only standard Lean
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
