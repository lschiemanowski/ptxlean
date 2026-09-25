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
a completed dense-layer execution, GPU execution, or speed.
The cooperating-thread foundations now include a memory graph derived from
actual repeated barriers and a separately checked two-round execution witness.

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

The instruction-to-memory adapter selects explicitly relaxed access forms:
`st.relaxed.cta.shared.u32` and `ld.relaxed.cta.shared.u32` for the single CTA's
shared storage, and GPU-scoped relaxed global accesses. These are not silently
substituted for weak shared instructions. The common graph uses disjoint location
codes for the two allocations and the existing all-in-scope word constraints.
It does not extend those constraints to mixed sizes, aliases, proxy changes or
arbitrary PTX dependent concurrency. No vendor prose is redistributed.

## Deriving memory order from the execution

`ParallelHistory.completed_arrivals` proves a property of every candidate run
from a reset barrier: any recorded completion has earlier actual arrivals by
every thread with exactly the same CTA, resource, generation and instruction
site. A completed phase is therefore an event in the trace, not a convenient
annotation supplied by the proof's caller. Arbitrary schedules and resource
reuse are allowed.

`ParallelMemory` projects the actual accesses into one graph. Non-memory events
still take up positions, so a store's place relative to a barrier is preserved.
The projection checks the issuing thread, fetched instruction, executed
predicate and access direction. `run_graph_complete` proves that a successful
memory access cannot be silently dropped.

`run_read_from_unique_writer` connects this graph to the existing memory rules.
Suppose exactly one program instruction writes a scratch location during the
execution. If the store precedes its thread's arrival and the load follows the
completed phase, every admitted read-source choice must choose that store.
Initialization is a competing write, but the coherence and no-stale-read rules
exclude it as the load's source. The theorem does not assume the loaded value.
Ownership and timing are explicit structural obligations for the concrete
kernel; a later overwrite would violate the uniqueness premise.

The reduction design consequently chooses fresh scratch for every round. This
spends more shared storage and needs an explicit total storage bound, but no
round can overwrite a previous round's input. Reusing storage later would need
a separate proof that every reader has finished.

## A completed two-round witness

`ParallelReference` chooses concrete array reads and the checked software FP32
result. Its soundness theorem shows that the selected steps belong to the
candidate execution relation. This is useful for existence, but does not by
itself prove memory admission or restrict the universal candidate relation.

`ParallelPublication` supplies both execution and admission proofs for a small
program. Its inputs `a` and `b` are arbitrary binary32 words. Define
`ab = add.rn.f32(a,b)` and `ba = add.rn.f32(b,a)` using the software reference;
the proof does not rely on their encodings being identical.

| Stage | Thread 0 | Thread 1 | Shared storage afterwards |
| --- | --- | --- | --- |
| Input publication | Load `a`, store slot 0 | Load `b`, store slot 1 | `[a,b,0,0]` |
| First `bar.sync 0` | Arrive and wait | Arrive and release | Same contents |
| Computation | Load slot 1, compute `ab`, store slot 2 | Load slot 0, compute `ba`, store slot 3 | `[a,b,ab,ba]` |
| Second `bar.sync 0` | Arrive and wait | Arrive and release | Same contents |
| Output | Load slot 3, store output 0, exit | Load slot 2, store output 1, exit | Same contents |

Both threads execute the same ten-instruction list with different supplied
address registers. The witness uses an alternating schedule; the interpreter
does not require lockstep execution. `successful` checks every dispatch status,
`completed` checks both exits and both arrays, and `memory_safe` derives the
alignment and bounds of every access.

The memory graph contains eight initial writes and twelve program accesses.
`graph_actual` equates its labels with the actual trace projection.
`serial_certificate` checks the sources, their values, coherence and ordering
against a chronological rank. `admitted` derives the original memory constraints;
`grounded` separately excludes cycles through ordering and read-source edges.
`admitted_execution` collects the execution, output and admission results.
These proofs are symbolic in `a` and `b`, including exceptional encodings; they
make no claim of real-valued accuracy for such encodings.

## The exact remaining obligation

A full parallel-layer theorem still needs its fetched kernel program. The
generic history, event-projection and single-writer publication results are
available, and the computed two-round witness demonstrates their compatibility.
They do not yet establish the layer's scratch ownership, phase timing, padded
reduction values, or an admitted complete layer execution.

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
lake build PtxDenseVJP PtxBinary32.ReductionRelu PtxBinary32.ParallelPublication
```

Lean checking establishes the stated formal results. Source review assesses the
connection to documented PTX semantics; neither establishes hardware conformance.

[barrier]: https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#parallel-synchronization-and-communication-instructions-bar
