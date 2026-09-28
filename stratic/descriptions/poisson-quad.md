# Quadrilateral Poisson solver

The example computes a steady field on the unit square from a supplied source,
with the field fixed to zero on the boundary. Poisson's equation states that the
negative sum of the field's second spatial derivatives equals that source.
A finite-element approximation represents the field by values at shared nodes
of a uniform square mesh. Q1 through Q4 select polynomials of degree one through
four in each coordinate within each cell.

The mesh uses Gauss–Lobatto interpolation nodes, including both cell endpoints.
Adjacent cells share endpoint nodes. Gauss–Legendre quadrature approximates an
integral by a weighted sum of values at selected points. One-dimensional basis
values and derivatives are reused in each coordinate. The operator acts through
successive small TorchLean matrix products instead of constructing the full
global stiffness matrix. Contributions at shared nodes are added, and solving
uses only interior unknowns; boundary entries are extended by exact zeros.

The executable reference uses Lean's native Float (binary64) on the CPU.
Its tensor contractions call TorchLean's matrix multiplication specification,
instantiated with Float. The same local algebra can be instantiated with real
numbers; this does not equate rounded execution with exact real arithmetic.
Quadrature setup computes Legendre roots by bounded Newton iteration rather
than reproducing PyTorch's eigensolver. Node, weight, operator and solution
comparisons check this numerical choice independently. No bitwise equality to
PyTorch's backend is promised.

The linear solver is Jacobi-preconditioned conjugate gradients: it uses the
operator's diagonal to rescale the iterative updates. It returns convergence,
breakdown or iteration-limit status. Success requires a newly computed residual
(the load minus the operator applied to the candidate solution) within the
requested tolerance. A small recursive residual alone cannot certify success;
false recursive convergence restarts from the measured residual. All loops have
explicit finite limits, and invalid mesh sizes, degrees, tolerances, vectors and
quadrature setup are rejected.

A sine solution with a known source supplies a reproducible end-to-end example.
Separate quadrature estimates measure errors in the field and its gradient;
these are numerical measurements, not proved bounds on the continuous equation.
The first implementation includes mesh/setup, operator and diagonal, load,
interior restriction, iterative solve and error integration. The reference does not include
differentiation through the solver or binary32 mode,
and it does not establish a convergence theorem, a finite-element error theorem or a verified numerical
relationship to the Python backend. Tests and any Lean theorems state their
own narrower guarantees.

A separate binary64 PTX backend runs the repeated matrix-free operator and
conjugate-gradient arithmetic on the GPU, using the Lean reference for mesh,
quadrature, load and diagonal setup. Its empirical comparison, memory checks
and execution evidence are distinct from a formal PTX correspondence theorem.

Accepted GPU solutions additionally pass a proved exact residual checker. It
uses the rational values represented by the saved binary64 setup and solution,
requiring zero boundary values and the requested bound for the discrete
interior equations. This certificate accounts for the returned rounding errors
without claiming identical CPU/GPU iterates, guaranteed convergence, or
accuracy relative to the continuous equation.
