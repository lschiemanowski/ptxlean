# Quadrilateral Poisson in Lean and TorchLean

This is a numerical port of `fem_0/standalone/poisson_quad.py`. It solves

```text
−(∂²u/∂x² + ∂²u/∂y²) = f    on the unit square
                     u = 0    on the boundary
```

The runnable example uses `u(x,y) = sin(πx) sin(πy)` and
`f(x,y) = 2π² sin(πx) sin(πy)`. The known solution lets us measure the error.
The implementation supports Q1–Q4: polynomials of degree 1–4 in each coordinate
on each square cell. Adjacent cells share their edge nodes.

## Run

Use the existing [pinned integration environment](../../integration/torchlean/README.md).
From the repository root:

```sh
cd integration/torchlean
lake --no-cache exe poissonQuad 8 4
```

The arguments are cells per side and polynomial degree; both are optional and
have defaults `8 4`. The program prints JSON containing the mesh, setup tables,
load, operator applied to a sample vector, solution, convergence status and
error estimates. An unsuccessful solve returns a nonzero exit code. No Python,
GPU, external solver or new package is needed to execute the Lean example.
The first native build can take longer than subsequent runs.

For controls or multiple cases, create a JSON array, for example:

```json
[
  {"n": 8, "degree": 4, "rtol": 1e-10, "maxiter": 1000, "check_every": 10},
  {"n": 2, "degree": 3, "source": "polynomial"}
]
```

Run `lake --no-cache exe poissonQuad --request INPUT.json --output OUTPUT.json`.
Supported source names are `sine`, `polynomial`, `constant` and `zero`.
`atol` supplies an absolute residual tolerance. Optional `load` and `values`
arrays override the assembled load and the sample vector used to inspect the
operator. Batch mode returns one result or explicit error per request; its
process exit status alone does not certify that every case converged.
Continuous error estimates are null for an overridden load or a source without
an accompanying exact solution. Nonfinite report values are null, not invalid
JSON. Finite report values retain the exact binary64 value.

## What is implemented

[PoissonQuad.lean](../../integration/torchlean/PoissonQuad.lean) follows the Python
file's numerical stages:

1. Construct shared Gauss–Lobatto nodes and uniform square cells. These nodes
   include endpoints; the interior nodes depend on the polynomial degree.
2. Compute Gauss–Legendre integration points and weights. Tabulate the Lagrange
   basis functions, which are one at their own interpolation node and zero at
   the others, and their derivatives.
3. Gather each cell's values into a TorchLean tensor. Apply the operator through
   small matrix products in each coordinate, without assembling a global matrix.
4. Add each cell's contribution into shared global entries. Compute the diagonal
   and the load vector using the same basis tables and integration weights.
5. Solve only for interior values using Jacobi-preconditioned conjugate gradients.
   This iterative method uses the diagonal to rescale updates. Boundary values
   are zero when the interior vector is extended to the full mesh.
6. Estimate errors in the solution and its gradient with a separate integration
   rule using one extra point per coordinate.

In the tensor formulas, rows are the **y** coordinate and columns are **x**.
With basis table `B`, derivative table `D`, quadrature-weight matrix `W` and
cell values `U`, the actual local computation is:

```text
dx    = (B U) Dᵀ
dy    = (D U) Bᵀ
local = (Bᵀ (W ⊙ dx)) D + (Dᵀ (W ⊙ dy)) B
```

Here `⊙` means entrywise multiplication. Every matrix product calls upstream
TorchLean's `Spec.matMulSpec`. This method is called sum factorization: apply
one coordinate at a time, rather than constructing a large cell matrix.
The cell-width factors in the gradient and area cancel for these two-dimensional
uniform square cells. The load retains the area factor `1/n²`.

The PCG loop preserves the source's important distinction: a small recursively
updated residual does **not** establish convergence. At the requested interval
and on the final step it recomputes `load − operator(solution)`. Only that
measurement can produce `converged`; false recursive convergence restarts the
iteration. Breakdown and iteration limits remain visible. Frozen loop steps
before the next scheduled check count as iterations, as in the Python source.

## Numerical and formal boundaries

This first port is **CPU binary64**, using Lean's native `Float`. It implements
the default numerical workflow; it does not port the Python CUDA/float32 modes,
backpropagation, or any PTX kernel. Public operator calls expect objects built
by `makeOperator`; manually replacing the mesh or its setup tables is outside
the contract. Node and degree validation occurs before setup, and supplied
vectors, sources and solver options are checked.

The local tensor definitions are generic in the scalar type and can also be
instantiated over exact real numbers. That is distinct from the executable
binary64 solver. The small zero-boundary helper has Lean proofs for boundary
and interior entries and is used in the executable extension. There is **no
proof yet** of the full assembly, conjugate-gradient convergence, finite-element
error, continuous PDE solution, numerical equivalence to Python, or hardware
behavior. Native arithmetic and transcendental functions are exercised by tests,
not certified by those boundary lemmas.

The consequential setup difference is quadrature: Python diagonalizes a small
Legendre recurrence matrix; Lean uses bounded Newton iteration on the Legendre
polynomial and evaluates the corresponding weights. Roots must converge within
64 steps and pass residual, domain and positive-weight checks. All rules needed
by Q1–Q4 are tested for integration of monomials through degree `2q−1`.
Scatter addition and tensor contractions have explicit sequential CPU orders;
they do not promise PyTorch backend bitwise equality.

## Checks and measured results

From the repository root:

```sh
python3 examples/poisson/check.py
```

This compares with frozen reference outputs using Python's standard library;
it builds and runs the actual Lean executable. For a live comparison with the
original file, use a Python environment containing Torch:

```sh
python examples/poisson/check.py --reference /path/to/poisson_quad.py
```

The committed reference identifies the Python source by SHA-256, the request
list, Torch version, precision and device. `--record` deliberately replaces the
fixtures and comparison report after a successful live comparison. A normal
check never updates expected results or tolerances.

The 22 numerical cases span all degrees, mesh refinement, zero and empty-interior
solves, iteration limits, scheduled checks and a polynomial manufactured solution.
For Q2–Q4, that polynomial lies in the finite-element space, giving an additional
check beyond the sine example. Lean-side checks also recover a small global
matrix by applying the operator to coordinate vectors, checking symmetry and
its diagonal; test constant functions and loads; and reject invalid inputs.
The normal integration checker runs these Lean checks and dependency audits.

The initial [comparison report](comparison.json) records maximum solution
difference from Python of about `2.22e-15`. For `n=8`, Q4, the Lean result is:

| Measurement | Value |
|---|---:|
| Interior unknowns | 961 |
| Loop steps | 10 |
| Relative true residual | 3.79e-14 |
| Solution error estimate (L2) | 1.05e-7 |
| Gradient error estimate (H1 seminorm) | 1.05e-5 |

These are empirical results for the recorded cases. In particular, the residual
measures how well the discrete linear equations were solved; it is different
from the solution's error relative to the continuous Poisson equation.
