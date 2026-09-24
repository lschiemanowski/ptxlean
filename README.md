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
its real-valued backward. This takes the same three inputs and an incoming
real-valued output weight `d`, and returns three real sensitivities:

```text
backward : ℝ × ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
backward(x,w,b,d) = (dx,dw,db)
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
axioms.` respectively. Both concrete examples above are included.

A smaller [array-loop example](docs/foundations/array-mask-select.md) combines
reviewed integer instructions with memory and branches, proving exact output,
memory safety and termination. After `lake build`, check it with
`lake env lean examples/array_mask_select.lean`.

## Sources and license

The [source ledger](docs/foundations/source-ledger.md) records interpretation of
the pinned NVIDIA PTX 9.4 documentation separately from checked proofs.
Project code is distributed under [Apache-2.0](LICENSE). NVIDIA documentation is
obtained separately from NVIDIA; upstream dependencies retain their own licenses.
