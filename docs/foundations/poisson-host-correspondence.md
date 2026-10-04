# From individual kernels to an accepted Poisson solution

The main entry points are now `Host.solver_exists` and `Host.accepted_solver`.
They answer different questions:

1. Can the finite driver actually execute its requested PTX kernels and return?
2. What is guaranteed about the stored solution when the exact check accepts it?

The first theorem constructs an execution. The second proves the requested
residual guarantee for any completed modeled execution whose actual output
passes the check. Neither says that every input converges.

## One iteration, following the bytes

The host uses one allocation for its uploaded tables, vectors and scalar fields.
`Host.Layout` describes their byte offsets, widths, bounds and separation. It
requires fewer than 2^30 nodes and cell entries, matrix width two through five,
and nonwrapping addresses. `Layout.Coefficients` fixes the emitted locations of
B, D and W, including their 32-byte guards. These conditions concern physical
storage, not desired numerical results.

Preparation launches `element_probe`, `assemble_probe`, `initialize`,
`dot_rhs`, `dot_rz` and `start`. The probe output is a diagnostic. Initialization
sets x to zero and builds rhs, r, z and p from the uploaded load, diagonal and
boundary flags. Start writes the norm, tolerance and initial status words.
The host reads those actual words to decide whether any iteration is needed.

An ordinary iteration requests:

| Entry | Effect |
|---|---|
| `element_p`, `assemble_ap` | Apply the operator to the search direction p. |
| `dot_pap` | Compute the reduction of p times ap. |
| `coefficient_alpha` | Compute alpha or disable the update according to actual status and operands. |
| `update_xrz` | Update solution x, recursive residual r and preconditioned residual z. |
| `dot_next`, `dot_rr` | Compute the next rho and recursive residual square. |
| `coefficient_beta` | Compute beta and the next flags. |
| `update_p` | Update the search direction. |

The output memory of each launch is the input memory of the next. `Host.Launch`
contains the actual fetched instruction runs and their memory-source evidence.
It does not replace a kernel with a mathematical function assumed to be correct.
Its vector, scalar, dot and cell cases reuse their existing complete execution
proofs. Every case also proves which bytes it may change.

`Layout.Static` says that all uploaded inputs remain byte-for-byte unchanged.
The footprint proofs establish this for each launch. Induction then preserves
it throughout the driver. In particular, later connectivity and assembly-table
loads still satisfy the original bounds. This is what permits the finite
execution theorem to construct the next kernel execution at every iteration.

## Checking and restarting

At the configured interval, and on the final iteration regardless of interval,
five further launches compute a fresh residual from the current x:
`element_x`, `assemble_ap`, `true_residual`, `dot_true`, `residual_norm`.
The CPU reads the resulting residual and status words. Its decision order is:

1. Nonfinite residual: breakdown.
2. Residual at or below the rounded tolerance: convergence.
3. Nonzero broken flag: breakdown.
4. Inactive solver: restart with `restart_vectors`, `dot_rz`, `restart_flag`.

This ordering matters. For example, a successful residual check precedes the
broken flag. Also, an inactive solver restarts even on the last iteration and
then returns `maxiter`. The Lean model retains both behaviors of the runtime.

Six preparation launches plus at most nine ordinary, five checking and three
restart launches per iteration give the bound `6 + 17 * maxiter`. The bound
holds for every completed modeled execution. Existence additionally uses the
concrete instruction witnesses, including padding threads and real barriers;
a bound on scheduling alone would not prove kernel termination.

The witness chooses a finite schedule. It does not prove that an arbitrary
physical GPU scheduler will make progress. NaNs, infinities and zero diagonals
do not invalidate raw instruction-execution existence. They can instead lead
to breakdown or rejection by the numerical check.

## Why acceptance is a second check

The GPU's residual calculation rounds. Its convergence flag is useful for
stopping but cannot establish an exact real-valued error bound by itself.
`Host.Certificate.decode` reads B, D, W, the load and tolerances from the
initial memory, and x from the actual final memory. Finite binary64 words
have exact rational values; the decoding theorem connects those values to
their real-number interpretation.

`Host.Certificate.problem` reads connectivity and boundary flags from those
same initial bytes. Its operator is the existing exact TorchLean tensor
operator. `Host.Certificate.accept` invokes the existing rational residual
checker on this problem and returned x. It does not use the reported norm.
If accepted, `Host.accepted_solver` proves:

- the original uploaded inputs are unchanged;
- the finite launch bound;
- the exact relationship between decoded values and actual stored words;
- zero solution at boundary nodes;
- the interior Euclidean residual bound
  `‖b − A x‖₂ ≤ max(atol, rtol · ‖b‖₂)`.

This is an a posteriori guarantee: recomputing the residual of the actual
answer establishes its accuracy. It does not require a theorem that PCG always
converges, nor equality with CPU iterates. The existing rounded operator and
kernel proofs explain what the implementation computes. The exact check
establishes the accepted answer's numerical guarantee despite that rounding.
A failure of the check is a failure to certify, even if raw `solve` returned
`converged`.

## The runtime connection and its limits

The in-memory theorem and archived-result checker share the exact residual
checker. The Python archive adapter extracts the coefficient words and repacks
the observed binary64 solution. The wire parser validates the uniform mesh and
reconstructs its boundary; the adapter checks that this boundary agrees with
the actual uploaded flags. Saved artifact hashes and negative tests protect
this path, but do not constitute a Lean proof of Python serialization or CUDA
transport.

`check_poisson_host.py` runs the actual Python `solve` with explicit mock kernels
and compares it with an evaluator of `Host.program`. The evaluator is proved
to follow `Host.Execution` for that supplied mock transition. The 168 cases
cover iteration/check budgets, restart, noncanonical nonzero flags, signed
zero, NaNs, infinities and branch precedence. They compare complete launch
lists, stop reasons, iterations, restarts and checked residual words. This
is source-fidelity testing of host control, not a GPU test or a replacement
for instruction proofs.

The restricted memory rules admit candidates using necessary source constraints;
they are not the full PTX memory model. Publication is mathematical reconstruction
from completed stores. Compiler correctness, CUDA visibility, hardware fidelity,
unconditional convergence, continuous PDE error and conditioning-based solution
error remain outside these theorems. The represented setup coefficients, rather
than ideal real-valued quadrature tables, define the equations being certified.

## Reading and checking the proof

Within `integration/torchlean/PoissonPTX`, read `HostSchedule.lean`,
`HostKernelLaunch.lean`, then `HostSolverCorrespondence.lean`. For the exact
acceptance semantics, follow `HostCertificateDecode.lean` and
`HostCertificate.lean`. `HostStorage.lean` and the four frame modules explain
input preservation. The [rounded-launch guide](poisson-rounded-launches.md)
and [cell-existence guide](poisson-cell-existence.md) explain the local witnesses.

Use the pinned toolchain and registered integration targets. On a resource
constrained machine, build only one Lean process at a time; this work was
checked with `-j1 -M5120` inside a 6 GiB cgroup with swap disabled and CPU quota
150%. Do not launch a fresh unrestricted whole-project build while the desktop
is already memory constrained.

After the registered `PoissonPTX.HostScheduleTest` target is built, the isolated
host-control comparison can be run from the repository root:

```bash
systemd-run --user --scope --quiet \
  -p MemoryMax=6G -p MemorySwapMax=0 -p CPUQuota=150% \
  python3 hardware/check_poisson_host.py --output /tmp/poisson-host-binding.json
python3 -m unittest discover -s hardware -p 'test_poisson*.py'
```

The checked-in host receipt records exact sources and comparison scope. The
integration audit separately checks exact theorem dependencies and rejects
unfinished proofs or new unchecked axioms. These changes do not require a new
GPU run and make no new empirical hardware-performance claim.
