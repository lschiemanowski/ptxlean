# A parallel dense–ReLU layer: program and verification boundaries

The target computation is

\[
x\in\mathbb R^n,\quad W\in\mathbb R^{m\times n},\quad b\in\mathbb R^m,
\qquad y=\operatorname{ReLU}(Wx+b)\in\mathbb R^m.
\]

**The complete selected forward execution is now checked in Lean, including
all reduction rounds, barriers, bias/ReLU stores and every thread's exit.**
The proof derives the stored binary32 words from the original inputs and connects
them to the existing conditional row error bound. It also preserves inputs and
proves access safety for the whole trace. **PTX memory-model admission and
correctness for every admitted execution remain unproved.** The final real-valued
padding identity connecting these row bounds to TorchLean's tensor graph is also
still open. There is no GPU execution or speed claim.

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

## The concrete forward program

`DenseProgram.lean` supplies a common instruction list, specialized to a shape.
It uses represented PTX instructions, including integer address arithmetic,
guarded loads and stores, separate binary32 multiplication and addition, and
`bar.sync 0`. It does not insert an abstract matrix multiplication or reduction
step. This is the internal instruction representation; PTX text parsing,
register declarations and the CUDA launch interface are separate obligations.

Choose a padded width `p = 2^depth` with `n ≤ p`. There are `m*p` threads in one
cooperating thread array. Thread `r*p+c` owns row `r` and column `c`.
For example, two rows with three inputs use eight threads when `p=4`.
Columns zero through two load inputs; column three uses zero without loading.

The global array has four consecutive slices:

| Words | Contents |
| --- | --- |
| `0 .. n-1` | Input vector x |
| `n .. n+m*n-1` | Matrix W, one row after another |
| `n+m*n .. n+m*n+m-1` | Bias b |
| Following m words | Output y |

Shared memory contains `depth+1` planes, each of `m*p` words. Plane zero holds
products. Every addition round writes to a new plane, so a consumer's inputs
are never overwritten by a later round. This is a simple ownership discipline
at the cost of additional shared storage. It is not a claim of an optimal kernel.

| Phase | Active work | Work required of every thread |
| --- | --- | --- |
| Products | Load `W[r,c]` and `x[c]` when `c<n`; otherwise use zero. Multiply and store plane zero. | Reach the first barrier. |
| Round k, from zero | Columns `c < 2^(depth-k-1)` read columns `2*c` and `2*c+1` from plane k, add, and store column c in plane k+1. | Reach the next barrier, including inactive columns. |
| Output | Column zero loads its row's root, adds bias, clears negative values to positive zero, and stores y[r]. | Exit. |

The program has `42+16*depth` instructions. The domain requires positive `m`,
`depth<32`, at most 1024 threads, and a conservative bound
`globalWords+sharedWords+2*p < 2^30`. The actual supplied arrays must cover their
required word counts. These bounds justify represented arithmetic; they are not
a GPU resource or launch-conformance theorem. An empty input can use `p=1` and
then computes ReLU of the bias. An empty output requires no launch, but a
formal wrapper for that case has not yet been added.

Only the thread ID and entry program counter are installed initially. Other
registers may contain arbitrary caller values. The program initializes every
operand used by the proved product phase, including the zeros for padding.
Byte pointers are calculated by widening a word index to 64 bits and doubling
twice. `DenseAddress.decoded_coordinates` proves the bit mask and shift compute
the intended row and column; `pointer_arithmetic` and `pointer_index` establish
the byte conversion and access bounds. `DenseLayout.scratch_injective` proves
that distinct round/row/column owners name distinct shared words. This layout
fact still needs to be connected to every later instruction's emitted access.

## From individual instructions to a complete selected execution

`ParallelSegment` composes ordinary instruction dispatches. Each segment must
prove that its instructions advance, leave the thread live and preserve the
barrier. `Segment.compile` additionally checks the segment's exact place in the
common program and an initially runnable thread. Thus a convenient arithmetic
calculation cannot masquerade as a fetched instruction execution.

`DenseSegments` proves pointer construction, coordinate setup and guarded
memory operations. `DenseProducts.product_segment` composes these into the
actual first 21 instructions for any thread, with no assumed loaded values.
The selected witness reads the concrete global array, and padding executes
without attempting an out-of-range load. `product_memory` calculates the exact
product written to that thread's slot.

`DenseProductPhase.product_phase_exists` then constructs an execution of all
threads through the first actual barrier. It proves that:

- every thread reaches instruction 22 alive;
- the barrier has completed and reset to generation one;
- every product slot contains the product calculated from its row's original
  inputs, including padded zeros;
- global storage is unchanged and shared storage retains its length;
- every emitted access is aligned and within its selected array.

The selected schedule runs all product segments, then the first barrier; each
addition round follows the same pattern. This is a finite witness for a parallel
program, not a requirement that arbitrary executions use this schedule, and not
a scheduler-fairness theorem.

`DenseRounds.round_regular` checks every instruction in a reduction segment.
The coordinates come from the thread's actual registers. An active column's
left and right addresses are proved in bounds; inactive columns skip their
loads, floating-point addition and store. `round_effect` derives the exact
fresh-plane write and proves that other threads' lane states are unchanged.
`round_fetch` locates that segment in the actual common instruction list.

`DenseRoundPhase.PlaneReady` describes the state just after a barrier: threads
are at the next round's entry, their coordinate registers are initialized, and
the previous plane holds its calculated tree values. `RoundInvariant` tracks a
sweep through the threads. Stores go to the new plane, so every earlier plane
stays unchanged. `round_reads` obtains operands from that preserved storage;
the proof does not receive their desired values as assumptions. The round then
executes all barrier arrivals and establishes `PlaneReady` for the next plane.
Induction on the number of rounds gives `reduction_exists`, including depth zero.

`DenseOutput` checks the bias and activation instructions for both leaders and
inactive columns. The activation is the actual unsigned sign-bit comparison and
conditional register clear, not an abstract machine instruction. Positive and
negative zero therefore produce positive zero. Each thread then fetches its
exit. `DenseForward.OutputInvariant` keeps the input region unchanged while
row leaders fill separate output words; already completed threads cannot be
modified by a later thread's segment.

`selected_forward_exists` combines those proofs. For every supported shape,
sufficient input/shared allocations and arbitrary caller register seeds, it
constructs a complete candidate execution with:

- every thread halted at its exit instruction;
- output row r equal to `forwardWord s originalGlobal r`;
- every input-region word unchanged;
- unchanged global and shared allocation lengths;
- all `depth+1` barriers completed and the barrier resource reset;
- every emitted memory access aligned and in bounds.

This is symbolic in all input words, including exceptional encodings. A
real-valued error statement needs additional conditions. `DenseArithmetic` maps
the plane-indexed calculation to the balanced-tree arithmetic relation.
`selected_forward_accuracy` now applies that bound to the words **actually
stored by the complete candidate**, under the existing `RowInput` conditions:
finite operand interpretations, encoding errors, calculated intermediate-range
checks, and a tree and bias that match the original input array. It does not
assume intermediate numerical accuracy. The real tensor/padded-tree identity
still needs to be proved before claiming the TorchLean correspondence.

The witness chooses concrete array reads and the checked software binary32
results. That is sufficient to construct steps in the candidate machine. It is
not yet a certificate that the trace's memory graph satisfies PTX's memory rules.
Nor does one selected completed execution prove that every permitted execution
has the same numerical guarantees. The unrestricted candidate relation and its
arithmetic result freedom have not been narrowed to obtain this proof.

## Checked memory replay and read origins

The selected execution now carries `ConcreteRuns` evidence: its scalar loads
use the current global or shared array. Forgetting that evidence gives the
original `Runs` relation, so existing candidate-execution results still apply.
The narrower witness relation does not alter which floating-point results or
candidate loads the general semantics permits. `ConcreteSegment` and the
concrete barrier-round witness preserve this evidence through the entire proof.

`ParallelReplay` independently checks the emitted memory events. It starts with
the supplied arrays, checks alignment and bounds, compares each recorded load
value with the current word, and applies each store. Global and shared arrays
remain separate. Non-memory events leave these arrays unchanged. The theorem
`concrete_replays` proves that a concrete-read execution always passes this
check and reproduces both final arrays. `reject_wrong_load` proves that changing
a load's word makes its replay fail even if the address remains valid.

`ParallelReplaySources.load_source` goes further. Split the trace immediately
before a particular load. Either there was no preceding store to that location
and the load uses the initial word, or the proof identifies a preceding store
with the observed value and proves that no later event before the load stores
to that location. The source is an event in this execution, not an assumed
correct intermediate value. Repeated writes and writes to the other memory
space are handled by the same theorem.

`DenseReplay.selected_forward_checked` exposes these facts alongside every
complete-forward guarantee listed above. It derives replay and read origins
from `selected_forward_concrete`; callers provide only the same shape, storage
bounds and register seeds as before.

Replay alone does not check instruction fetches or synchronization, and does
not prove PTX memory admission. The execution proof supplies the former facts;
the remaining admission proof must map the derived sources into the existing
memory graph, construct the order of writes to each location, and discharge all
memory and barrier constraints. These obligations have not been replaced with
replay or added as assumptions of the dense theorem.

## Software regression checks

`DenseChecks` runs the complete instruction list through `ParallelReference`.
The cases cover two rows and three inputs padded to four, an empty input with
two biases, a one-input activation exactly at zero, and a two-row power-of-two
case. Both activation branches are exercised. Caller registers, address
registers, output and shared storage start with nonzero sentinel values so
accidental reliance on zero initialization is exposed.

Each case checks successful statuses, every thread's exit and final program
counter, outputs, unchanged inputs, allocation lengths and the final barrier
generation. Each case also replays the emitted memory events and compares both
final arrays. The integration checker evaluates these cases afresh even when
Lean build artifacts are cached. These are executable tests of the selected
software semantics, not general Lean proofs, memory-admission proofs, GPU runs
or performance measurements.

## The exact remaining obligation

The next step is a memory-admission certificate for the complete selected trace.
Concrete-read replay and latest preceding store origins are proved; constructing
the indexed graph sources and write ordering and proving their compatibility
with the actual barrier certificate remain open.
For correctness over arbitrary admitted executions, the proof must additionally
derive each actual writer and the access positions relative to barrier arrivals
and completion. The existing generic memory-order results can then force the
permitted read sources. The selected array-read calculation must not be used as
a premise that an arbitrary read is fresh.

The stored row bounds must then be connected to the actual TorchLean matrix
graph, including the identity removing the padded zero terms, while preserving
permitted arithmetic results. The empty-output no-launch wrapper and the
separately supplied parallel backward kernel with stored `dx`, `dW`, and `db`
correspondence remain additional work. The Stratic component stays partial.
No GPU run or benchmark is needed for these proof obligations.

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
lake build PtxBinary32.DenseForward
lake env lean PtxBinary32/DenseChecks.lean
```

Lean checking establishes the stated formal results. Source review assesses the
connection to documented PTX semantics; neither establishes hardware conformance.

[barrier]: https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#parallel-synchronization-and-communication-instructions-bar
