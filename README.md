# PTXLean

PTXLean is a Lean formalization of NVIDIA's PTX instruction language. It targets **PTX instruction set architecture (ISA) 9.4**. A central goal is allowing to prove that kernels written in PTX implement functions specified in e.g. TorchLean.

This is very early alpha. Full coverage of PTX is the eventual goal.

This project has been realized with GPT 6 Astra and Luna.

The code is accompanied by descriptions managed in
[stratic](https://github.com/lschiemanowski/stratic).

The project currently includes:

- **31 instruction families** with 53 documented forms, from integer and bit
  operations to selected floating-point instructions.
- **An execution model** covering threads, registers, memory access and ordering,
  shared memory, block barriers, and multi-block grids.
- **ReLU MLP layers and softmax**, with forward/backward computations connected
  to TorchLean by execution and numerical-error theorems.
- **A higher-order quadrilateral finite-element solver** for the Poisson problem
  on a square, including a binary64 GPU implementation and proved residual
  certification. The solver's PTX–TorchLean correspondence is work in progress.

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

## Example: a ReLU neuron

A single neuron multiplies its input by a weight, adds a bias, and applies ReLU,
which replaces negative values with zero:

```text
F(x,w,b) = max(w*x + b, 0)
```

The example connects a binary32 PTX implementation to this real-valued computation
in TorchLean, with a proved bound on the error in the stored output.

### The PyTorch computation

With scalar tensors `x`, `w` and `b`, the computation is:

```python
import torch

def neuron(x: torch.Tensor, w: torch.Tensor, b: torch.Tensor) -> torch.Tensor:
    return torch.relu(w * x + b)
```

### The TorchLean computation

The corresponding definition in [PtxReluVJP.lean](integration/torchlean/PtxReluVJP.lean)
expresses the same three operations as a graph: multiply `w` by `x`, add `b`,
then apply ReLU. Here the tensors contain exact real numbers (`ℝ`), so this graph
specifies the mathematical computation to which we will compare the rounded
PTX result.

```lean
abbrev scalarShape : Shape := .scalar

def inputs (x w b : ℝ) : TensorPack ℝ [scalarShape, scalarShape, scalarShape] :=
  .cons (Tensor.scalar x) (.cons (Tensor.scalar w) (.cons (Tensor.scalar b) .nil))

def rawGraph : Graph [scalarShape, scalarShape, scalarShape] [scalarShape, scalarShape, scalarShape] :=
  let x : Idx ([scalarShape, scalarShape, scalarShape] ++ []) scalarShape := ⟨⟨0, by simp⟩, rfl⟩
  let w : Idx ([scalarShape, scalarShape, scalarShape] ++ []) scalarShape := ⟨⟨1, by simp⟩, rfl⟩
  let p : Idx ([scalarShape, scalarShape, scalarShape] ++ [scalarShape]) scalarShape := ⟨⟨3, by simp⟩, rfl⟩
  let b : Idx ([scalarShape, scalarShape, scalarShape] ++ [scalarShape]) scalarShape := ⟨⟨2, by simp⟩, rfl⟩
  let a : Idx ([scalarShape, scalarShape, scalarShape] ++ [scalarShape, scalarShape]) scalarShape := ⟨⟨4, by simp⟩, rfl⟩
  ((Graph.nil.snoc (TapeNodes.mul w x)).snoc (TapeNodes.add p b)).snoc (TapeNodes.relu a)

def graph : Runtime.Autograd.Torch.TypedGraph ℝ [scalarShape, scalarShape, scalarShape] scalarShape where
  nodeShapes := [scalarShape, scalarShape, scalarShape]
  data := rawGraph.toAlgebra.toData
  output := PtxTorchLean.output scalarShape
```

`scalarShape` means that each tensor contains one number. The function `inputs`
wraps the three real numbers in scalar tensors and collects them in the order
`[x, w, b]`. `TensorPack` records each tensor's shape in its type; the nested
`.cons` constructors build that collection, ending with `.nil`.

`rawGraph` describes how new values are computed from this input collection.
In its type `Graph [scalarShape, scalarShape, scalarShape]
[scalarShape, scalarShape, scalarShape]`, the first list describes the three
inputs and the second describes the results of the three appended nodes.
`Graph.nil` starts with no computed nodes. Each `.snoc` appends one node, which
can read the original inputs and any earlier node's result.

As the graph is evaluated, its collection of available values grows as follows.
Positions are numbered from zero:

| Position | Value | Supplied or computed by |
| --- | --- | --- |
| 0 | `x` | First input |
| 1 | `w` | Second input |
| 2 | `b` | Third input |
| 3 | `p = w*x` | `TapeNodes.mul w x` |
| 4 | `a = p+b` | `TapeNodes.add p b` |
| 5 | `max(a, 0)` | `TapeNodes.relu a` |

The `let` bindings in `rawGraph` name **references to these positions**. For
example, `p` refers to position 3, where the multiplication result will be
available. An `Idx` records both an in-range position and the expected tensor
shape. The lists joined by `++` describe the inputs plus the results available
at that stage: addition can refer to `p`, and ReLU can refer to `a`.

Finally, `graph` packages this construction as a `TypedGraph` with three scalar
inputs and one scalar output. `nodeShapes` lists the shapes of the three computed
values; `rawGraph.toAlgebra.toData` supplies their evaluation data.
`PtxTorchLean.output scalarShape` selects position 5, the ReLU result, as the
output. Thus `graph.forward (inputs x w b)` evaluates the nodes in order and
returns that final scalar tensor. `Tensor.item` extracts its single real value.

The theorem `forward_value` states that this evaluation gives exactly the
mathematical neuron expression for every real `x`, `w` and `b`:

```lean
theorem forward_value (x w b : ℝ) :
    Tensor.item (graph.forward (inputs x w b)) = max (w*x+b) 0
```

### Forward PTX

The forward computation uses **two separate launches**: the first stores the
affine value `A`, and the second applies ReLU. These are the actual instruction
bodies. Symbolic address registers such as `%x` are supplied at launch;
`%r0`–`%r4` hold 32-bit words. Register declarations, address setup and host launch
wrappers are outside the verified example.

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

Multiplication and addition round separately to nearest, with ties to even.
The ReLU gate tests the binary32 encoding with integer comparisons: zero has all
bits clear, and the high bit marks a negative value. For finite values this
implements ReLU, returning positive zero for either signed zero. It is a small
reference implementation, with no claim about ReLU's NaN policy.

### The theorem connecting them

[`stored_forward_accuracy`](integration/torchlean/PtxReluAccuracy.lean) says that
**every completed execution of the two PTX launches satisfying the assumptions
below stores a finite result within an explicit error bound of the TorchLean
computation**. Its statement is:

```lean
theorem stored_forward_accuracy (i : Inputs d)
    (present : before.cells allocation = some ⟨thread.device,d.words⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before (forwardStages.map (request target thread allocation registers)) after) :
    ∃ (out : Data) (y : ℝ), after.cells allocation = some ⟨thread.device,out.words⟩ ∧ finiteReal out.y = some y ∧
      |y-TorchLean.Tensor.item (ReluVJP.graph.forward (ReluVJP.inputs i.x i.w i.b))| ≤ i.budget
```

The arguments before the conclusion describe the inputs, initial memory and
execution being compared:

- **`i : Inputs d` — the numerical assumptions.** `d` holds the initial binary32
  words. `i.x`, `i.w` and `i.b` are the ideal real inputs supplied to TorchLean;
  `i.xh`, `i.wh` and `i.bh` are the real numbers represented by the corresponding
  words in `d`. These need not be equal: for example, `i.ex` bounds
  `|i.xh - i.x|`, the input's encoding error. `i.ew` and `i.eb` do the same for
  the weight and bias. `Inputs` also requires finite encoded values and bounds
  the intermediate magnitudes so that multiplication and addition stay in range.
- **`present` — the initial storage.** In the initial store `before`, the
  allocation identified by `allocation` exists on `thread.device` and contains
  exactly `d.words`. This includes the inputs and initialized scratch/output
  slots; those slots may initially hold arbitrary bit patterns.
- **`eligible` — the target.** The modeled target uses PTX ISA 9.4 and has
  `sm ≥ 70`, as required by `Mixed.Eligible` for these instructions.
- **`chain` — the PTX execution.** `forwardStages` selects the affine computation
  followed by ReLU. Mapping `request` over these stages supplies their programs,
  addresses and initial registers. `Chain before ... after` records their
  completed instruction executions and writebacks, from `before` to `after`.
  Each launch uses one thread; the first launch's writes are visible to the
  second, with no intervening interference. A real runtime must establish this
  launch contract.

The conclusion starts with `∃ (out : Data) (y : ℝ)`: there are final data `out`
and a real output value `y` satisfying all three clauses joined by `∧`:

1. **`after.cells allocation = some ⟨thread.device,out.words⟩`** identifies the
   actual contents of the allocation after execution as `out.words`.
2. **`finiteReal out.y = some y`** says that the stored output word represents
   the finite real number `y`. Finiteness of the output is part of the conclusion.
3. **The final inequality** compares that `y` with the scalar extracted by
   `Tensor.item` from the TorchLean graph evaluated at the ideal inputs. By
   `forward_value`, that reference value is `max(i.w * i.x + i.b, 0)`.

Writing `E = i.budget`, the numerical guarantee is therefore:

```text
|stored output as a real number - max(w*x + b, 0)| ≤ E
```

The budget is computed from the inputs and their error bounds, rather than
chosen after seeing the output. It includes a rounding allowance for each of
the two arithmetic operations, plus the propagated input encoding errors:

```text
E = multiplication rounding allowance + addition rounding allowance
    + |w|*ex + |x|*ew + ew*ex + eb
```

Here `x` and `w` are the ideal real inputs, and `ex`, `ew`, `eb` are their
encoding-error bounds. The rounding allowances use the encoded operands and
the rounded intermediate product; their exact definition is
[`affineBudget`](integration/torchlean/PtxBinary32Error.lean).
Even if encoding is exact (`ex = ew = eb = 0`), arithmetic rounding can still
contribute error. The same bound applies when rounding changes which side of
zero the affine value falls on: there is no assumption that the PTX and
TorchLean ReLU gates make the same activation decision.

The [study guide](docs/foundations/relu-neuron.md) gives the detailed definitions
and execution conditions.

<a id="run-the-checks-and-examples"></a>

## Run the checks

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
and `Integration check passed: … exact dependency reports, only standard Lean
axioms.` respectively. The integration check reports the number of declarations
audited. Example-specific execution and GPU validation commands are in the
linked guides above.

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
