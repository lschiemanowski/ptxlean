# A parallel dense–ReLU layer: specification and execution foundations

The target computation is

\[
x\in\mathbb R^n,\quad W\in\mathbb R^{m\times n},\quad b\in\mathbb R^m,
\qquad y=\operatorname{ReLU}(Wx+b)\in\mathbb R^m.
\]

**This milestone establishes the actual TorchLean graph and generated backward,
rounded reduction arithmetic, and reusable parallel control and address-safety
proofs. It does not yet implement or verify the parallel dense-layer kernel.**
In particular, there is no claim about a completed layer's stored outputs,
multi-round PTX memory admission, GPU execution, or speed.

## The mathematical computation and its backward

Each row of W describes one neuron. Its affine value is
`a_i = sum_j W_ij*x_j + b_i`, and `y_i = max(a_i, 0)`.
The Lean tensors use `[n,1]` and `[m,1]` column shapes, allowing the actual
TorchLean matrix-multiplication node to express a matrix-vector product.
The weight shape is `[m,n]`; the dimensions need not be equal.

The incoming vector `d` describes how a later scalar loss changes with each
output: `d_i` is its sensitivity to `y_i`. This is the vector-Jacobian product
interface. It also allows a caller to choose a sensitivity vector directly,
without committing the layer to a particular loss.

First set `g_i = d_i` when `a_i > 0`, and `g_i = 0` otherwise. Then

```
dx_j    = sum_i W_ij * g_i
dW_ij   = g_i * x_j
db_i    = g_i
```

`PtxDenseVJP.lean` builds the graph from the pinned upstream matmul, add and
ReLU nodes. `generated_vjp` reduces the actual automatic backward, and
`backward_coordinates` proves the formulas above for its resulting tensors.
This is not a separate handwritten backward substituted for TorchLean's result.
`checked_result` also proves success of the upstream checked interface.

When every `a_i` is nonzero, `sensitivities_adjoint` identifies that result with
the adjoint of the ordinary real derivative. At zero, `gate_at_zero` establishes
the chosen zero convention, without claiming differentiability there. The empty
inner dimension gives `ReLU(b)`; with no outputs, all input sensitivities are
zero. These are mathematical graph results, not yet kernel edge-case results.

`PtxTensorContext.lean` supplies reusable identities for handling the graph's
collection of differently shaped tensors. It allows the proof to follow tensor
operations instead of expanding the arithmetic of one huge flattened index.

## Parallel arithmetic has its own rounding order

A scalar loop adds one product at a time. A parallel tree can combine independent
pairs in each round. For four entries the intended arithmetic is

```
p0 = round(w0*x0)     p1 = round(w1*x1)
p2 = round(w2*x2)     p3 = round(w3*x3)
q0 = round(p0+p1)     q1 = round(p2+p3)
s  = round(q0+q1)
a  = round(s+b)
y  = ReLU(a)
```

Each `round` denotes a separate round-to-nearest-even binary32 operation.
The sums must not be silently reassociated to match a sequential reference:
floating-point addition can give different results in different orders.
Bias and activation are intended to remain within the forward launch.

`PtxBinary32/Reduction.lean` defines a tree with actual binary32 multiplication
result contracts at its leaves and addition contracts at its forks.
`balanced_leaves` and `balanced_depth` establish the shape and input order of a
complete balanced tree. `eval_exists` supplies arithmetic result choices for
all input words; it is **not** an execution-existence theorem.

For numerical accuracy, each leaf carries finite encoded operands, ideal real
operands, encoding-error bounds and a product-range check. `Safe` checks each
rounded intermediate sum against the maximum finite magnitude, using expressions
calculated from the original operands. `accuracy` then derives finiteness and
an error bound for **every** admitted arithmetic choice. It does not assume the
accuracy of an intermediate result.

`ReductionRelu.lean` adds the bias, activation and backward gate. ReLU does not
increase the forward error. A strict margin `error < abs(idealAffine)` guarantees
that rounding cannot change the backward's branch. The seed's incoming error
then bounds the gate error. Propagation through the full matrix backward, padding
for non-power-of-two lengths, and the corresponding kernel proofs remain to be
connected; this arithmetic API does not claim those results.

## Threads, storage and repeated barriers

A cooperating thread array (CTA) is a thread group with shared storage and
barriers. The new `Parallel` machine fetches one common instruction list;
thread-specific data live in separate registers. A schedule chooses which thread
takes the next step. Integer operations reuse the existing scalar evaluator;
FP32 steps reuse the nondeterministic binary32 instruction relation.

Global storage and CTA-owned shared storage are distinct word lists. Every
memory instruction and trace event retains its selected space. An address check
requires a multiple of four bytes and an index inside that list. `runs_access_safe`
and `runs_memory_length` prove these bounds and fixed storage sizes for arbitrary
finite prefixes, including proposed load values and prefixes that later fault.
They do not prove initialization, allocation permissions, or termination.

The first barrier arrival records its instruction site. Waiting threads cannot
fetch past it. Completion requires every participant, clears the arrival set,
and advances a generation number before the resource is reused. `runs_aligned`
proves that waiting threads retain the common site. `release_aligned` therefore
justifies advancing all participating program counters on release.
`barrier_round_exists` gives a concrete increasing-thread schedule of fetched
arrivals; `two_barriers_exist` composes two rounds at successive instruction sites.
The witness ends just before exit and makes no fairness or termination claim.

The represented form is `bar.sync 0` with full participation and no early exits.
Other resources and forms are outside the slice. A resource operand outside this
slice is rejected by the interpreter; this does not make it illegal PTX.
The machine's numerical target condition selects PTX 9.4 and sm_70 or newer.
Physical thread-count limits and launch validation are not established here.

## What the source review does and does not justify

The local pinned PTX ISA 9.4 manual was checked against SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The barrier interpretation follows [§9.7.15.1][barrier], also discussed in the
[barrier source review](barrier-source-review.md) and
[shared-memory source review](shared-barrier-source-review.md): resource identity,
full participation, blocking, completion and reuse must remain explicit. The
all-thread condition specializes the full-CTA/no-early-exit discipline; it is not
a model of arbitrary warp divergence or barrier forms. The protocol's existing
`complete_iff_all_warps` relates all-thread completion to all represented warps.

A future instruction-to-memory connection must use the reviewed access forms,
such as explicit `st.relaxed.cta.shared.u32` and `ld.relaxed.cta.shared.u32`, rather
than silently interpreting weak shared loads/stores as relaxed operations.
The new machine's space tags alone do not establish those PTX memory labels.
No vendor prose or source artifact is added to the repository by this change.

## The exact remaining obligation

A full parallel-layer theorem still needs a fetched kernel program and a
multi-round memory argument. The existing concrete shared-memory proofs cover a
single publication window. The new generic machine deliberately allows proposed
read values; its barrier witness does **not** prove that a consumer receives the
preceding round's sum.

The next connection must derive a completed-phase ordering certificate from the
actual instruction history, label every memory event, establish write ownership
and lifetime for each scratch location, and show that every admitted graph forces
each consumer to read its producer. It must also construct an admitted complete
execution. Reused scratch needs protection against overwriting a value before
all readers finish; fresh per-round storage is another possible design with an
explicit size cost. No choice between those storage designs is hidden in the
current proofs.

Only then can the layer connect stored `y`, `dx`, `dW`, and `db` to the graph and
the error bounds, with padding, address calculations and dimension/launch limits
proved. Assuming the desired read values, using arithmetic-tree evaluation as
execution, or serializing the layer into the old scalar launches would leave
that obligation unresolved. The Stratic component remains partial for this
reason. No GPU run or benchmark is needed for these proof obligations.

## Reproduce the checks

From the repository root, with the pinned integration dependencies provisioned:

```sh
bash scripts/check.sh
bash integration/torchlean/check.sh
```

The second command builds the new modules and audits their public declarations'
transitive axiom dependencies, alongside the previous integration results.
No external model, GPU kernel or benchmark is invoked. For a shorter local build:

```sh
cd integration/torchlean
lake build PtxDenseVJP PtxBinary32.ReductionRelu PtxBinary32.ParallelBarrier
```

Lean checking establishes the stated formal results. Source review assesses the
connection to documented PTX semantics; neither establishes hardware conformance.

[barrier]: https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#parallel-synchronization-and-communication-instructions-bar
