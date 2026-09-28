# Run the quadrilateral Poisson solver on a GPU

This backend executes the [Lean/TorchLean Poisson example](../examples/poisson/README.md)
in binary64 PTX on an RTX 5090. It runs the matrix-free finite-element operator
and the arithmetic of the Jacobi-preconditioned conjugate-gradient (PCG) solve.
PCG repeatedly improves a candidate solution using residuals and search directions;
the diagonal rescales those directions. It does not construct a global matrix.

The kernels are authored in [poisson_kernels.py](poisson_kernels.py). They are
**empirically checked against Lean, not exported from a proved PTX program**.
The existing formal instruction model does not cover this binary64 backend.
Preserving the source's precision takes priority over reusing its binary32 model.
No formal numerical-refinement, PCG-convergence or continuous PDE-error theorem
is claimed, and no performance measurements are included.

## Run and replay

Use the project's [pinned Lean integration environment](../integration/torchlean/README.md),
Python 3.10 or newer, the NVIDIA driver, and a CUDA toolkit containing `ptxas` and
`compute-sanitizer`. This harness needs only Python's standard library; it does
not import Torch or install packages. From the repository root:

```sh
python3 hardware/validate_poisson.py \
  --output .hardware-runs/poisson-local \
  --ptx-version 9.2 --sanitizers
```

The output directory must be new. This builds the Lean executable, exports the
30 reference cases, assembles the kernels, runs comparisons, and replays the
saved binaries under all four sanitizers. Omit `--sanitizers` for numerical
checks alone. Results, solutions, generated PTX, GPU binaries, launch sequences,
input buffers and logs remain in the output directory; failures are retained.
For example, `12-n8-q4/observed.json` contains the recorded Q4 solution. `report.json` lists the authoritative case names and statuses.

The current reviewed target is `sm_120`. PTX 9.2 is an **explicit compatibility
selection** for the installed CUDA 13.2 toolchain, not an automatic fallback.
Omitting it requests PTX 9.4. See the [restricted instruction review](poisson-compatibility.md).
Other architectures have not been tested by this backend.

To reproduce the committed results without rebuilding or assembling:

```sh
mkdir -p .hardware-runs/poisson-replay
sha256sum hardware/receipts/poisson.tar.gz
# Compare with archive_sha256 in hardware/receipts/poisson.json.
tar -xzf hardware/receipts/poisson.tar.gz -C .hardware-runs/poisson-replay
python3 hardware/validate_poisson.py --replay .hardware-runs/poisson-replay/poisson
```

Replay verifies the saved artifact hashes, checks the reconstructed input layout,
loads the saved binaries and compares the complete observations, including launch
order and convergence decisions. It does not rebuild Lean or compile PTX. This
is a same-target reproducibility check, not a portability guarantee.

## Where each computation happens

| Stage | Execution |
|---|---|
| Mesh, interpolation nodes, integration rules, basis tables | Lean CPU |
| Load and Jacobi diagonal | Lean CPU |
| Incident-element lists and packing setup buffers | Python CPU |
| Local operator and assembly into global node values | PTX GPU |
| Vector updates, diagonal division, dot products, coefficients, norms | PTX GPU |
| Kernel scheduling and convergence-status decisions | Python CPU |
| Independent residual cross-check on the returned GPU solution | Lean CPU and Python |

Setup arrays are transferred once. Solver vectors stay in GPU storage through
iteration; the CPU reads scalar residuals and flags at scheduled checks. A
separate operator probe and the final solution are copied back for inspection.
The Python source is connected through the existing CPU comparison suite;
this GPU suite directly compares against a fresh export of the Lean reference.

Each cell gets one cooperative thread array (CTA), a group of 32 threads that
can exchange shared memory and synchronize at barriers. Only `(degree+1)²`
threads compute matrix entries. All 32 threads reach every barrier. Five stages
compute the same tensor formula as `Poisson.localAction`:

1. Gather the cell's nodal values `U`.
2. Compute `B U` and `D U`.
3. Compute the two derivatives and multiply by integration weights.
4. Apply transposed basis and derivative tables.
5. Complete both contractions and add their contributions.

The two-dimensional uniform-square scaling is inherited from the Lean operator.
Each cell writes to its own output region. A second kernel gives each global
node one writer, summing incident cells in ascending cell order. There are no
floating-point atomic additions. Boundary entries are set to zero for the
interior solve; the unrestricted operator probe retains them.

Small matrix contractions have explicit sequential sums and separate rounded
multiplications and additions. Dot products use 256 threads: each sums strided
entries, then a shared-memory tree combines their partial sums. This order
differs from the CPU loop, so iteration histories and bits need not coincide.
The single-group dot product is a simple baseline, not a scalability claim.

PCG preserves scheduled checks of the true residual `load − operator(solution)`.
Recursive convergence freezes updates until that check; a failed true-residual
check restarts from the measured residual. Zero loads, empty interiors, an
iteration limit and numerical breakdown are distinct outcomes. The new suite
observed no restarts, so that branch is implemented but not exercised by these
recorded runs. Extremely scaled inputs can overflow even in binary64 and return
breakdown; the solver does not promise convergence for every finite input.

## Recorded evidence and its limits

The [receipt](receipts/poisson.json) records the exact code and artifact hashes,
Lean version, toolchain and selected device. The run used an RTX 5090, driver
610.57.04 and `ptxas` 13.2.78 with separate multiply/add instructions.

All 30 cases passed their specified checks: 27 converged, two deliberately hit
iteration limits, and one huge finite load produced the expected breakdown.
Cases span Q1–Q4, mesh refinement, polynomial reproduction, zero and empty
interiors, non-polynomial operator probes, and longer constant-load solves.
The latter include 56 and 72 loop steps. On these cases:

- Every unrestricted operator probe matched Lean exactly.
- The largest solution-coordinate difference was `2.22e-15`.
- Boundary solutions remained zero and all input/guard bytes were preserved.
- `memcheck`, `racecheck`, `synccheck` and `initcheck` all passed on full-suite replay.

Tolerances are fixed in the runner: operator differences allow
`2e-12 + 2e-12 * |reference|`, solution differences allow
`2e-11 + 2e-9 * |reference|`, and polynomial reproduction allows `2e-12`.
These empirical acceptance thresholds are not proved error bounds.

Each converged result must satisfy the GPU's requested true-residual tolerance.
Independently, Lean applies its operator to the GPU solution and Python computes
the residual norm. Comparing that measurement allows `2e-12 + 2e-10 * residual`;
corroborating convergence allows an additional absolute `2e-12`. Thus the check
does not prove that the independently measured residual meets an arbitrarily
tight requested tolerance exactly. An algebraic residual also differs from the
error relative to the continuous Poisson equation.

Input checks and finite index bounds restrict the generated layout. Guard bytes
surround every logical buffer, and all read-only bytes are checked after solving.
Sanitizers add evidence about the tested executions; they do not prove memory
safety for all mesh sizes. The backend uses ordinary weak global/shared loads
and stores, with CTA barriers and ordered kernel launches for synchronization.
There is no claimed connection to the project's formal relaxed-access model.
