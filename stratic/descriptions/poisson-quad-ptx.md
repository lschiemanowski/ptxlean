# Poisson PTX backend

The binary64 PTX backend performs the repeated matrix-free Poisson operator
and preconditioned conjugate-gradient (PCG) iterations on the GPU. Matrix-free
means applying the operator without storing the full global matrix. The Lean
reference supplies the mesh, quadrature, load and diagonal setup; the diagonal
rescales the residual to form the preconditioner. Supported uniform square
meshes use polynomial degrees one through four and homogeneous zero boundary
values. Numerical inputs use binary64; indices and flags use unsigned 32-bit
words.

Each cell has one 32-thread block. Threads gather its input values, perform
the ordered tensor contractions through seven shared matrices and four barriers,
and store separate element contributions. Assembly gives each global node a
single writer that adds contributions in element order. No floating-point
atomic addition is needed. Vector launches use whole blocks of 256 threads,
with out-of-range threads returning before memory access. Dot products use
one 256-thread block, strided partial sums and a fixed eight-round reduction
tree. Their rounded order is part of the algorithm.

One persistent guarded allocation contains the uploaded coefficients and
indices, working vectors and scalar status. PTX kernels initialize the solver,
compute coefficients, update x/residual/search direction, recompute the fresh
residual and restart when requested. The CPU driver only schedules launches,
reads status and stops on convergence, breakdown or the iteration limit.
The formal host model uses those actual published status bytes and derives
preservation of the uploaded data from the kernels' actual writes.

Valid storage and index tables admit a complete finite modeled execution of
all requested launches, with at most `6 + 17 * maxiter` launches. Each launch
contains actual fetched instructions, returns and necessary byte-source
constraints. This proves existence of a terminating model schedule; it does
not prove convergence or progress under every hardware schedule.

Correspondence is established in separate layers. The tensor calculation and
ordered assembly must first agree with the Lean specification without assuming
associativity of rounded addition. A binary64 instruction interpretation must
then connect actual register and memory execution to those calculations. The
parallel dot-product order is part of the GPU algorithm, so the solver's result
is not required to be bitwise identical to the CPU PCG loop.

A successful rounded convergence status alone does not certify the solution.
An exact checker reads the represented coefficients and returned solution words,
checks zero boundary values and recomputes the interior residual over rational
numbers. Acceptance proves `‖b − A x‖₂ ≤ max(atol, rtol · ‖b‖₂)` for those same
represented equations. The complete host theorem binds this gate to the actual
final solution memory. Neither CPU iterate equality nor an empirical numerical
allowance is substituted for the requested residual bound.

The hardware runner saves source, launch metadata, input storage, observed
outputs and provenance. Validation compares the operator and solver against
the Lean reference, audits unchanged inputs and buffer guards, and requires
exact certificates for cases reported as converged. PTX text-binding checks
compare generated entries with the Lean instruction representations. Host
control tests compare the Python driver with the Lean model using mock launches;
they do not execute or verify the numerical kernels.

These are distinct kinds of evidence: model proofs, source-fidelity checks,
exact result certificates and empirical GPU observations. Full PTX memory
admission, compiler correctness, external serialization and transport, CUDA
visibility, GPU conformance and scheduling fairness remain outside the
restricted formal claim. No continuous PDE accuracy or unconditional PCG
convergence is asserted.
