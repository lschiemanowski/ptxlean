# A parallel dense–ReLU layer: program and verification boundaries

The target computation is

\[
x\in\mathbb R^n,\quad W\in\mathbb R^{m\times n},\quad b\in\mathbb R^m,
\qquad y=\operatorname{ReLU}(Wx+b)\in\mathbb R^m.
\]

**The complete selected forward execution is checked in Lean, including all
reduction rounds, barriers, bias/ReLU stores and every thread's exit.** The same
trace has a proved admission certificate under the existing restricted memory
model, preserves inputs and satisfies access safety. **Its stored binary32
outputs approximate the actual TorchLean real tensor graph**, under explicit
input-encoding and calculated finite-range conditions. The proof removes padded
zero terms from the real sum, including for an empty input. Correctness for every
admitted execution remains unproved. There is no GPU execution or speed claim.

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
zero. The selected forward kernel also covers empty inputs; an empty-output
no-launch wrapper remains to be supplied.

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
then bounds the gate error. Propagation through the full matrix backward and its corresponding kernel
proofs remain to be connected. The forward padding and tensor connection are
proved separately, as described below.

## From stored words to the actual tensor graph

`PtxDenseForward.Encoding` states how the initial words represent `x`, `W` and
`b`. Each weight/input pair carries its finite real interpretation, the ideal
tensor entries, their encoding errors and a product-range check. Biases have
the same kind of interpretation and error bound. The remaining range checks
apply to the explicit rounded reduction tree and its bias addition. These are
conditions on calculations from the original operands, not assumptions that
unknown execution intermediates already have the desired accuracy.

`ReductionPadding.paddedInput` fills columns beyond the input length with exact
positive-zero operand pairs. `padded_ideal` proves that their ideal real sum is
just the sum over the original input coordinates. This also handles zero input
columns: all leaves are zero and the ideal affine value is the bias. It permits
real-number associativity only. The binary32 calculation still contains every
padded leaf and addition, in the fixed tree order, and its error budget retains
those nodes. The bound is conservative; it need not be zero for an exactly
representable result.

`Encoding.row_words` connects that numerical tree to the actual operands loaded
by the kernel. `Encoding.row_ideal` identifies its ideal sum plus bias with the
coordinate of the actual TorchLean affine graph. `forward_word_accuracy` then
uses ReLU's non-expansion of error to compare the reference output word with the
actual TorchLean graph output. No activation margin or nonzero-affine premise is
needed for this forward result; those conditions belong to backward branch and
derivative arguments.

Finally, `PtxTorchLean.DenseForward.selected_forward` returns one admitted,
terminating instruction execution whose stored output at every row is a finite
binary32 word within the derived error bound of that graph coordinate. Its
memory-admission certificate, stored values, preserved inputs, final allocation
lengths, barrier state and access-safety proof all refer to the same execution.
The caller supplies the initial encoding and range conditions, not a tensor/tree
identity, desired load values or a premise about intermediate accuracy.

The comparison is to TorchLean's real-valued tensor specification. It is neither
bitwise agreement with a concrete PyTorch run nor a theorem about all admitted
kernel executions. Arithmetic bounds already quantify over permitted arithmetic
results, but that alone does not prove the necessary memory observations for
arbitrary thread schedules.

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

## Control facts for arbitrary forward executions

An instruction position identifies a slot in the common program; a trace
position identifies an event in one particular interleaving of threads. They
are different numbers. A store at instruction 20 can appear anywhere in the
combined trace, depending on which other instructions ran first.

The dense instruction list has no jumps. Its scalar instructions either
advance to the next slot, fail without emitting an event, or are skipped by a
false predicate and still advance. Its explicit parallel exit halts the thread.
`DenseControl.program_straight` checks this property against the complete list,
including every reduction round.

`ParallelControl.runs_progress` proves that each thread's recorded instruction
positions increase strictly. The argument permits arbitrary load candidates,
all allowed binary32 result choices, arbitrary scheduling and incomplete runs.
For the proof, a thread has a measure `2*pc` while runnable and `2*pc+1` while
waiting or halted. Ordinary instructions advance the position; arrival or exit
consumes its current position; completion advances all participants past the
barrier. The measure never decreases. It is derived from the existing machine
state and introduces no new scheduling rule.

Consequently, `DenseControl.scalar_site_unique` rules out two occurrences of
one thread's store site. `trace_store_site` also classifies every actual store,
using its fetched instruction and emitted memory effect:

| Instruction position (starting at zero) | Storage | Role |
| --- | --- | --- |
| `20` | Shared | Product publication |
| `22 + 16*k + 14`, for `k < depth` | Shared | Reduction-round publication |
| `22 + 16*depth + 18` | Global | Row output |

This is not yet a proof that two different threads cannot calculate the same
address. Site uniqueness and location ownership are distinct obligations.

`ParallelCompletion.completion_split` locates the actual release step in an
arbitrary trace. Alignment, which is already proved from the reset state,
places every participant at that barrier site before release and at its next
instruction afterwards. `completion_orders_sites` therefore proves that events
before completion have instruction positions at or below that site, and events
after completion have positions strictly beyond it. A barrier site cannot
complete twice in this program.

These facts discharge timing from instruction-site inequalities. A producer
at an earlier site precedes its own actual arrival, and a consumer at a later
site follows the observed completion. `ParallelVisibility.run_read_from_unique_writer_sites`
uses these derived facts in the existing memory rule, preserving its explicit
requirements for an admitted graph, actual producer and consumer occurrences,
and exactly one program writer to the location. It does not assume that the
load used the desired value.

Computed-address ownership and existence of producers and completed phases
are established below. Connecting each consumer load to its producer and the
allowed arithmetic results to stored outputs remains a separate argument.

## Why arbitrary tensor values cannot change store ownership

`DenseOwnership.graph_writer_unique` proves that two noninitial writes to the
same location in the exact memory graph must be the same graph entry. It covers
arbitrary candidate schedules, proposed load words and permitted binary32
results. It does not assume admission, successful completion, desired outputs,
zero-initialized registers or the selected software runner's read choices.

The proof separates the values being computed from the addresses that carry
them. The dense program keeps its thread number in register 0, column in 1,
row in 2, weight index in 3 and temporary address index in 7. Data registers
4, 5, 6 and 8 contain tensor values and arithmetic results. Predicate 0 decides
which columns are active. Predicate 1 tests the sign of a tensor result and
only controls a data-register update for ReLU.

`ParallelAddressControl.Agree` compares only the program counter, integer
registers 0/1/2/3/7, all address registers and predicate 0. The projection
calculates pure address/control arithmetic, omits memory data and floating-point
results, and ignores guards on writes to omitted state. This is sound only under
`ProgramCompatible`: retained updates must be unconditional and depend only on
retained inputs; loads and floating-point operations cannot overwrite retained
registers. `DenseAddressControl.program_address_compatible` checks every
instruction of the supplied list. Compatibility is proved, not added as a caller
assumption to the dense theorem. The current retained set fits this kernel;
another register convention would need a generalized projection or another
compatibility proof. This keeps the proof aid small without changing the machine.

Induction over actual machine steps preserves agreement with the projected
prefix at each thread's current instruction. A scalar skip still advances;
an arbitrary floating-point result changes only omitted data; barrier release
advances every waiting participant from the aligned barrier site. A tensor load
may propose any word, but cannot alter the address calculation.
`ParallelStoreControl.run_store` then connects each emitted store's actual byte
address to that prefix. If the store is guarded by predicate 0, it also recovers
that the projected predicate is true. Ignoring this last condition would allow
nonleader output stores into the ownership argument.

Writing `T=rows*width` and `t` for the thread number gives:

| Store | Derived byte address | Additional fact |
| --- | --- | --- |
| Product | `4*t` | Scratch plane 0 |
| Round `k` | `4*((k+1)*T+t)` | Scratch plane `k+1` |
| Output | `4*(outputBase+t/width)` | `t % width = 0` |

All formulas are derived at the actual store sites, using the existing shape
bounds to rule out 32-bit index or 64-bit pointer wraparound. Dividing a shared
word offset by `T` identifies its plane; the remainder identifies its thread.
For global output, equal offsets identify equal rows, and the proved column-zero
condition identifies the issuing thread. Strict instruction order then rules
out a second execution of that thread's store site. Global and shared memory
have distinct location codes even when their numeric byte addresses match.

Finally, `Memory.program_write_origin` traces each noninitial graph write back
to its actual scalar store. Trace-position uniqueness and the graph's existing
unique labels give `graph_writer_unique`. Initial contents are deliberately
excluded: initialization and the later program store are distinct writes.
The result proves **at most one** program write. The next section supplies
producer and barrier existence for completed runs. Visibility still requires
matching the consumer's address and applying the admission constraints. In particular, it does not turn a faulting or
incomplete prefix into a completed forward computation.

## Recovering producers and barriers from a finished execution

A proposed read value may be arbitrary before memory admission, and a schedule
may leave a thread waiting indefinitely. Neither fact permits a completed run
to omit an earlier instruction. `ParallelCoverage` makes that distinction
precise without restricting read values or assuming scheduler fairness.

The argument starts with the actual `halted` flag. In a program without scalar
exits or jumps, a lane can become halted only by executing a fetched parallel
exit. `halted_exit_origin` recovers that event. `DenseCoverage.fetched_exit_site`
checks the complete dense list: its only exit is at `22+16*depth+19`. The earlier
control-order theorem then bounds the final instruction counter below by that
site. The caller supplies completion, not a desired final counter or a list of
instructions claimed to have executed.

`crossing_step` uses a simple discrete fact: a machine step advances any given
thread's instruction counter by at most one. If a run starts before a site and
ends beyond it, some actual step changes its counter from that site to the next.
The theorem retains the run prefix, crossing step and suffix. Other threads'
steps, faults, waiting and halted stutters cannot skip over the site. A barrier
release advances every participant by one; alignment proves that all of them
were at the same synchronization site.

Two cases then matter:

- At a memory instruction, the crossing step is that same thread's scalar
  evaluation, with its actual emitted occurrence. Another thread's barrier
  release cannot impersonate a memory instruction because its fetched site
  contains a barrier instead.
- At a synchronization instruction, crossing requires an actual release and
  completion event. An arrival alone leaves the instruction counter unchanged.
  `completed_phases` therefore recovers the product barrier and every reduction
  barrier from the trace. The existing history theorem recovers every
  participant's earlier arrival with exactly that completion's key.

A scalar occurrence alone does not prove a store happened: a false predicate
also advances the instruction counter. `completed_store_exists` inverts the
successful scalar evaluation only after establishing its guard. The dense
corollaries discharge that condition from the previously proved projection:
products are unconditional, round `k` uses columns below `2^(depth-(k+1))`, and
output stores use column zero. The projection's round predicate is proved from
its comparison instruction with no-wrap bounds; it is not an assumed active
thread mask. Thus `completed_product_store`, `completed_round_store` and
`completed_output_store` recover real memory effects at their proved addresses.
Initial contents and skipped instructions cannot stand in for these stores.

The publication theorems package each shared-store producer with the actual
phase it precedes. Strict instruction order proves the producer occurs before
its own arrival, using the barrier-history theorem's arrival position. This
holds across arbitrary interleavings and arbitrary candidate tensor values.
Combined with ownership, it supplies existence, uniqueness and producer timing.

These are conditional facts about runs that reached exit. They require no new
allocation-length premise because crossing a store already entails a successful
address check. This does not establish termination for an arbitrary schedule,
produce a new execution witness, or bypass the memory-admission check. Depth
zero has the product barrier and no reduction-round obligations; padded inactive
columns are not incorrectly required to emit a guarded round store. The existing
selected execution still supplies the independent nonvacuous completed witness.

The next obligation is to derive consumer-load addresses and active-column
relationships, match each to one of these producers, and apply memory admission
to force the read source. Only then can the permitted floating-point operations
be connected to the numerical reduction tree for every admitted execution.

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
results. Constructing those steps alone does not establish memory admission.
The separate certificate below now supplies that proof. One selected completed
execution still does not prove that every permitted execution has the same
numerical guarantees. The unrestricted candidate relation and its
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
the admission proof below maps the derived sources into the existing memory
graph and discharges its memory and barrier constraints. These obligations have
not been replaced with replay or added as assumptions of the dense theorem.

## From read origins to an admitted execution

`ParallelChronology` gives each graph event a position in a strict chronological
order. Initial writes come first; program events use their positions in the full
instruction trace. The graph's existing list groups accesses by thread, so list
indices themselves would not give the required chronology. The proof retains
that list and adds a separate rank. Initial location codes occupy a bounded
range; program ranks start beyond that range. Two distinct graph entries cannot
have the same rank, because one trace position identifies one issuing thread
and one memory event.

Program-order edges point forward in this ranking. So do the cross-thread edges
obtained from actual barrier arrivals and completions. The represented accesses
are relaxed loads and stores, so no release/acquire-pattern edge is silently
assumed. Global and shared addresses continue to use distinct location codes.

`ParallelSources.source_exists` converts the replay origin of each load into an
index in this exact graph. The source is a write to the same location, with the
observed value, strictly before the read. Every other write to that location
before the read is no later than the source. This covers both initialization
and repeated program stores; it does not require the kernel to have only one
writer per address.

`ParallelAdmission` selects these proved sources and orders same-location writes
chronologically. The source selection uses Lean's ordinary classical choice:
it is an existence proof, not an executable graph-extraction tool. The theorem
`concrete_certificate` proves every field of the existing `SerialCertificate`,
including initial-write order and the barrier-induced edges. Its existing
soundness theorem gives `Graph.Ordered.Valid`; the memory constraints themselves
are unchanged. The same ranks exclude cycles made from those order edges and
read-source edges. This is a sufficient selected witness, not a proposed rule
that all PTX executions must follow one global sequential order.

`DenseAdmission.selected_forward_admitted` applies that reusable result to the
complete dense-forward execution. Its admission graph, terminating instruction
run, stored row words, unchanged inputs, allocation lengths and access safety
all concern the same trace. The theorem also gives the existing `RowInput`
error bound for its actual stored words. Shape, storage and numerical premises
are unchanged; graph validity, desired read values and output accuracy are not
new assumptions.

The admission theorem is relative to the restricted memory model described in
this project. It does not establish hardware conformance or full dependent PTX
semantics, scheduler fairness, or correctness of every admitted layer execution.

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

The complete selected trace is admitted. Arbitrary candidate traces now have
proved instruction order, unique thread/store-site occurrences, exhaustive
store-site classification, computed-address ownership, at most one program writer
per memory location and derived timing around observed completed barriers.
Completed executions also supply every required producer and completed phase,
with scratch stores before their actual arrivals. For correctness over every
admitted completed execution, the proof must still derive consumer addresses
and match each load to its unique producer. The visibility rule can then force
read sources and connect the allowed arithmetic results to each stored output.
The selected array-read calculation must not be used as a premise that an arbitrary read is fresh.

The selected stored row bounds are now connected to the actual TorchLean
matrix graph, including zero-padding removal. Extending that correspondence to
every admitted execution must preserve permitted arithmetic results and prove
the required memory observations. The empty-output no-launch wrapper and the
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
lake build PtxDenseForward PtxBinary32.DenseCoverage PtxBinary32.ParallelVisibility
lake env lean PtxBinary32/DenseChecks.lean
```

Lean checking establishes the stated formal results. Source review assesses the
connection to documented PTX semantics; neither establishes hardware conformance.

[barrier]: https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#parallel-synchronization-and-communication-instructions-bar
