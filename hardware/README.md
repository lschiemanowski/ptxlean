# Run the verified dense–ReLU forward on a GPU

This harness runs the existing parallel computation `y = ReLU(Wx + b)` on an
NVIDIA GPU. Its PTX body is emitted from the same Lean instruction list used by
`PtxTorchLean.GridDenseForward.universal_forward`. It compares GPU output with
the Lean arithmetic reference, independent exact rational arithmetic and ordinary
PyTorch CUDA execution. It stops at forward: no backward, softmax or benchmark
is included.

The current reviewed target is an RTX 5090 (`sm_120`, compute capability 12.0).
The first recorded run uses CUDA 13.2, driver 610.57.04 and PyTorch 2.11.0+cu130.
Other hardware targets need an explicit adapter review. The formal domain is
rows with at most 1024 input columns, padded to a power of two. One group
computes each row; the total thread count may exceed 1024. Empty output vectors
skip launch, while empty input vectors return ReLU of the bias.

## Run

Provision the project's pinned Lean dependencies as described in the
[integration README](../integration/torchlean/README.md). Use Python 3.12 with
`hardware/requirements.txt` installed, NVIDIA's CUDA toolkit (`ptxas` on PATH),
and a working CUDA driver. To create a separate Python environment explicitly:

```sh
uv venv --python 3.12 .hardware-runs/venv
uv pip install --python .hardware-runs/venv/bin/python -r hardware/requirements.txt
```

This installs the exact PyTorch wheel requested by the harness; its transitive
Python environment is not a fully locked distribution. Run receipts record the
actual Python, Torch, CUDA and compiler versions and dependency revisions.
There is no downloaded installation script.

From the repository root, choose a fresh output directory:

```sh
.hardware-runs/venv/bin/python hardware/validate_dense.py \
  --output .hardware-runs/dense-forward \
  --ptx-version 9.2 --target sm_120 --sanitizers
```

The explicit 9.2 option matters: the initial machine's assembler and driver
reject 9.4. The formal model stays at 9.4; the emitted older subset has a
[documented compatibility review](ptx-compatibility.md). Omitting this option
requests 9.4 and fails if unsupported. No automatic version fallback occurs.

The command verifies pinned Lean dependencies, builds the current exporter and
forward proof, exports the formal instruction lists and arithmetic references,
assembles the PTX, and runs every case three times. Body memory instructions
explicitly retain the model’s relaxed ordering and GPU/global or CTA/shared scope. It then runs four
GPU-only replays under Compute Sanitizer: memory access, shared-memory race,
synchronization and uninitialized-read checks. Omit `--sanitizers` for a normal
comparison run; the report explicitly says those checks were not run.

For GPU-only replay of the saved artifacts, including on the recorded toolchain:

```sh
.hardware-runs/venv/bin/python hardware/validate_dense.py \
  --replay .hardware-runs/dense-forward
```

Replay verifies input, export, PTX and binary hashes before execution. It does
not regenerate or silently recompile the saved kernel. Standalone CPU tests are:

```sh
python3 -m unittest discover -s hardware -p 'test_*.py'
```

The main integration checker also builds and audits the Lean exporter and runs
its rejection tests. Hardware checks remain a separate command, so checking
proofs does not require a GPU.

## Meaning of a pass

All four paths start from exactly the same binary32 input words, interpreted
as exact real values for the mathematical reference. There is no unaccounted
input conversion error.

1. **GPU versus Lean:** each output word must match `Dense.forwardWord` bit for
   bit, including the kernel's zero-sign behavior. This reference has the same
   multiplication, balanced tree-addition and bias order as the formal program.
2. **Exact numerical check:** Python `Fraction` arithmetic independently rounds
   each operation to binary32, compares that result with Lean, and computes
   the ideal real `ReLU(Wx+b)` exactly. It checks every product, tree addition
   and bias addition against the formal finite-range premise, and computes
   `Reduction.RowInput.error` with zero input-encoding errors. Every observed
   output must satisfy that bound. Python's evaluator is reviewed and tested,
   not itself verified in Lean.
3. **Ordinary PyTorch:** `torch.relu(W @ x + b)` runs on CUDA in FP32, with
   TF32 disabled and no autocast or graph compilation. Its different arithmetic
   order may give different bits. The report records its exact error from the
   rational answer separately from the kernel's error.

For PyTorch, the diagnostic allowance is
`(k*u*sumAbs + k*2^-150)/(1-k*u)`, where `k=2*n+2`, `u=2^-24`, and `sumAbs`
is the sum of absolute real products plus the absolute bias. This is a
conservative engineering check motivated by ordinary FP32 rounding; it is not
a proved bound for the concrete PyTorch backend. Exceeding it fails the run and
preserves the case. We never replace our kernel's theorem-derived allowance
with this diagnostic tolerance.

Forward ReLU needs no away-from-zero derivative condition. Near-zero affine
values are valid forward test cases. The backward's activation-margin premise
is a different obligation and is not tested here. Nonfinite inputs or exact
intermediates beyond the formal finite range are rejected by the numerical
checker; they do not count as supported accuracy cases.

## Cases and artifacts

The suite combines hand-chosen padding, empty-dimension, signed-zero, subnormal,
rounding-tie, cancellation and unfused-arithmetic cases with seeded random inputs
across row widths up to 1024. Multiple output rows use distinct groups sharing
one global allocation. Checks also require unchanged input storage and allocation
guard words. Sanitizers inspect actual fetched hardware behavior but are not
universal proofs of race freedom, hardware conformance or scheduler progress.

Each fresh output directory contains the exact input words, Lean instruction
manifest, arithmetic reference, PTX, compiled cubins, assembler logs, GPU and
PyTorch observations, and a JSON report. The report includes source hashes,
formal and emitted PTX versions, device/toolchain identity, launch dimensions,
all coordinate errors and allowances, repeated-run count and sanitizer outcomes.
Failures retain the inputs, artifacts and an error record; there is no tolerance
relaxation or case dropping.

The first published evidence is described in [the results note](results.md).
