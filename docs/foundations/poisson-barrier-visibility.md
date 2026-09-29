# Why a later thread reads the published value

A shared store and a shared load are separate operations, possibly executed by
different threads. A proof of the store's value alone does not determine what
the load observes. The synchronization proof connects them.

Consider a small fragment in which thread zero writes a word, thread one skips
that work, both reach `bar.sync 0`, and both then read the word. A second barrier
uses resource zero again. Skipping work does not exempt thread one from either
barrier.

## Instruction execution and memory sources

`PoissonPTX/Concurrent.lean` executes a common program using each thread's actual
program counter. Arithmetic uses the existing binary64 instruction relation;
a store records its computed byte address and source operand. A load can choose
any eight-byte word. This deliberately permits an old-value candidate before
checking whether its sources are legal. `ConcurrentOrigins` ties every recorded
access to a data instruction fetched in an actual execution prefix.

Global and shared addresses are kept in separate spaces. The per-thread state
retains storage fields to reuse local instruction definitions, but candidate
loads do not obtain their values from those fields. Cross-thread read values
come from the later source constraints. Consequently these local storage fields
do not assume that every thread reads from one memory updated immediately by
every preceding store.

The combined `skip active target` instruction represents a conditional forward
branch using the fixed comparison between the thread index and the number of
active matrix entries. It abstracts the already-computed `%live` predicate;
this fragment does not prove the full kernel prologue or model arbitrary changes
to that predicate. The active branch advances to the body. Padding branches land
at the actual barrier target, as proved by `padding_reaches_barrier` when that
target contains `sync 0`.

## What the barrier proof establishes

The machine reuses `Ptx.Barrier`, whose state records an arrival bit for every
participant. The first arrival fixes the instruction site for the current use
of barrier zero. A request at a different site or resource cannot release it.
Waiting threads cannot fetch more instructions. Completion resets the arrival
bits, advances every participating thread beyond the barrier, and increments the
reuse number. This distinguishes successive uses of the same barrier resource.

`ConcurrentHistory.completed_arrivals` proves that each completion in a fetched
execution has earlier actual arrivals from all participants at that exact site
and reuse number. This holds for arbitrary candidate runs, not just the schedule
chosen by an example. `ConcurrentBarrier` constructs finite execution witnesses
for a whole round and two successive uses. It does not promise that an external
GPU scheduler chooses those schedules or prove termination of the whole solver.

`ConcurrentOrder.access_after_barrier` also derives the ordering of later memory
accesses. If the program contains a barrier at a given instruction position and
no branch from before it can jump past it, every access at a later position has
an actual completion and all participants' arrivals in its earlier history.
This holds for every schedule and candidate read value, and does not assume the
phase's result. Instantiating the condition requires checking branch targets.

## Why the producer cannot skip its store

The completion history alone does not yet connect the producer's computation to
the barrier. The producer must execute its store before arriving. A program
counter is simply the position of the next instruction a thread will execute.
`ConcurrentProducer.StopsFor` checks the branches before a required store: for
this producer, each branch either takes the active path or lands at or before
the store. The condition allows padding threads to skip the body, but it cannot
be used to claim that such a thread produced a value.

`store_before_arrival` proves that reaching a later barrier arrival forces an
earlier store event from that producer. Arithmetic advances one instruction at
a time, branches obey the condition above, and a barrier cannot release threads
past a store because all releasing threads must be at the same barrier site.
The proof retains each event's position in the history, even when records at
two positions happen to have identical contents.

`producer_across` joins this result with the consumer-side barrier theorem. For
any candidate execution with a later read, it derives the strict sequence

```text
producer's store < producer's arrival < common completion < consumer's read
```

These are positions in the same actual execution history. The theorem takes
fetched instruction and branch facts, not an assumed ordering path or a computed
matrix answer. It applies to arbitrary interleavings of the participating threads.

## Why there is only one writer

Different matrix lanes write different eight-byte words; different temporary
planes occupy separate storage. That geometric fact alone is insufficient:
a thread might visit a store twice if the program contained a loop.
`ConcurrentOwnership.Forward` rules out backward branches in the fragment.
`access_site_unique` then proves that each thread emits at most one access at
any instruction position. Waiting at a barrier does not count as another store.

`PlaneStores` records the remaining structural obligation for a kernel: every
shared store comes from an active lane, targets that lane's word in one of the
seven planes, and occurs at that plane's designated instruction. It constrains
addresses and instruction positions, not stored values. `plane_sole_writer`
combines this coverage with disjoint byte ranges and the non-repetition proof
to identify the unique actual store event covering a word.

`read_from_plane_producer` composes these control and ownership results with the
byte-source rules below. A read of the producer's plane entry must recover that
producer's actual stored word, byte for byte. The theorem no longer takes an
assumed barrier path or assumed unique-writer event. It still requires the
kernel's structural branch and plane-coverage conditions to be proved. For the
complete generated Poisson cell, this instantiation and the connection to the
local contraction results remain unfinished.

## Why old bytes are excluded

`BarrierSources.Compatible` requires each read byte to come from initial memory
or a matching byte of an actual executed store in the same address space.
`BarrierSources.Across` identifies a store, its issuing thread's arrival, the
common barrier completion, and a later read in the actual history.

The primitive `Performed` constraint excludes initialization as a byte source
when a covering shared write precedes that completed barrier. This is our
explicit formal interpretation of the relevant PTX barrier guarantee, not a
fact proved by Lean about NVIDIA hardware. Source review checked PTX ISA 9.4's
`bar` and `st` sections, using the locally pinned manual SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
Ordinary shared stores have no synchronization of their own; completion of the
whole-block barrier makes preceding writes available to its participants.

Under the additional restriction that exactly one program store can cover the
shared word, `read_from_writer` derives both the read value and the source of
every byte. It does not assume the expected matrix answer or whole-word atomicity.
`read_published` then connects the read to a snapshot containing that store's
word. The earlier shared-plane publication proofs establish such snapshots from
completed stores; their full-cell instantiation is still required.

This fragment assumes that no outside thread writes the locations, all
participants belong to the same thread block, and accesses use the ordinary
memory-access mechanism (called the generic proxy in PTX). Different numeric
addresses never refer to the same physical byte. The source constraints
deliberately omit the rest of PTX's rules for deciding which executions are
allowed. A compatible execution witness in this model is therefore not
by itself a complete PTX-admission or GPU-conformance result.

## Checked examples and remaining work

`BarrierChecks` executes the two-thread fragment from concrete initial states.
It proves that an old-value candidate can execute and has compatible initial
byte sources, but violates the barrier's `Performed` constraint. A new-value
candidate has compatible sources and satisfies that constraint. The resulting
read theorem derives the stored value from those rules. Other checks exercise
barrier reuse, a missing inactive participant, and the last missing participant
of a 32-thread block. Without a barrier, the necessary constraints permit an
old-value source; this is a constraint witness, not a full PTX-admission claim.

`ProducerChecks` reuses that executable fragment with the newly derived ordering
and ownership. Its ordering theorem covers every candidate execution of the
fragment, not only the example schedule. The concrete read theorem discharges
plane coverage from the executed history and recovers the stored value through
`read_from_plane_producer`. Negative checks reject a padding thread as the
required producer and a branch that would bypass the barrier.

The saved-PTX checker also verifies the five-phase control skeleton of each
Poisson element entry: five matching guards and labels, four unpredicated
`bar.sync 0` boundaries, the expected lane predicate, no internal control transfer
or predicate modification in the bodies, and the final return. Mutation tests
reject a skipped, moved, predicated, or renumbered barrier. This is a syntactic
frontend check, separate from the Lean theorems.

## Applying the proof to the actual middle phases

`CellMiddle` gives the actual instruction program for phases 1–3 of the generated
cell kernel. A plane is one temporary matrix stored in shared memory. The slice
starts just after phase 0 has gathered the input and synchronized the threads.
It ends after phase 3 has stored its outputs and completed another barrier.

| Phase | Computation in this slice | Shared outputs |
| --- | --- | --- |
| 1 | Two contractions using the gathered input | Planes 1 and 2 |
| 2 | Two contractions, each multiplied by its integration weight | Planes 3 and 4 |
| 3 | Two contractions using the weighted intermediates | Planes 5 and 6 |

All 32 threads run the guards and barriers. Only the first m² lanes enter the
arithmetic bodies, where m is the matrix width (2 through 5 for Q1 through Q4).
The input plane's bytes are actual initial storage for this slice; the theorem
does not assume they already represent the desired gathered tensor.

The address proof uses two small, separately proved invariants:

- `ConcurrentPadding` shows that inactive lanes remain at guards, barriers, or
  the end of the slice. They emit no load or store events.
- `ConcurrentAddress` tracks the preparation of the two address scratch
  registers. Immediately before a shared store, the widened lane index and
  shared base have been added by the actual preceding instructions. A branch
  may not land halfway through that preparation. The shared base and lane
  registers retain their initial values.

`CellMiddle.Checked` is a finite check of instruction structure. It verifies
these branch and register restrictions and identifies every shared store's
plane and instruction position. `CellMiddleChecks` proves the checks with Lean's
kernel for the four emitted layouts: basis offset 0, derivative offset 8m²+32,
and weight offset 16m²+64, measured in bytes from the global arena base. Another
arena layout requires another structural certificate; the generic address proof
itself is parameterized by the program. Initial data and candidate read values
are not enumerated or fixed by these certificates.

`CellMiddleChecks.coverage` derives the plane-ownership condition from arbitrary
candidate runs of these concrete programs. `unique` then identifies each word's
only actual writer. `publication` joins these results with the barrier proof:
a later read at a producer's plane address recovers its actual stored word,
including the source of all eight bytes, under `Compatible` and `Performed`.
Within this slice, the later reads consume planes 1–4. Planes 5 and 6 are
produced here but consumed by the final phase outside this slice.
The caller supplies initial PCs, lane/base registers, storage-size conditions
and the read's location—not an assumed coverage or barrier-ordering relation.

The frontend compares **every instruction** of the three bodies with this Lean
program, including the weight loads and multiplications. It also checks the
associated guards, branch labels and barriers. This is stricter than matching
the contraction and store sub-blocks alone, and remains a frontend check rather
than a verified general PTX parser. Mutation tests reject changed weights,
extra writes to the shared base, incorrect addresses and missing/reordered phases.

`CellMiddleWitness` supplies a finite Q1 candidate execution from zero storage:
four active threads execute the bodies, 28 padding threads skip them, all 32
participate, and all threads finish after three releases. This witnesses the
candidate instruction machine. `CellMiddleNumericChecks` additionally proves
that its actual zero-valued loads and computed stores satisfy both necessary
source constraints, and applies `completed_middle` to it. The proof follows
chosen loads compositionally and derives the store values from the numerical
invariant. A small checked representation lemma ensures decoded positive zero
has the actual zero bits. This witnesses the theorem's premises for Q1; it does
not prove arbitrary-input existence or complete PTX memory admission.
Negative checks reject an in-range but wrong matrix coordinate and addition
in place of the integration-weight multiplication.

The full generated cell kernel is **not yet proved**. The reusable connection between candidate loads, actual stored words and the
ordered TorchLean contraction proof is described below. Its numerical
instantiation for the concrete middle phases is now proved, as detailed below. The gathered input, complete
prologue, final addition/output and whole-cell composition also remain open.
The publication theorem does not identify its stored word with a mathematical
or TorchLean coordinate by itself. Complete PTX admission, hardware progress
and whole-solver correspondence retain their separate boundaries.

Run the checked proofs and regression tests from the repository root:

```sh
integration/torchlean/check.sh
python3 -m unittest discover -s hardware -p 'test_*.py'
```

The saved-artifact binding check is described in
[the cell contraction guide](poisson-cell-contractions.md).

## From interleaved instructions to a computed value

Barrier visibility answers “which store supplied these bytes?” It does not yet
answer “what did that store compute?” The replay proof joins these questions.

Consider one thread between the start of a contraction and its final shared
store. Other threads can execute in between any two of its instructions.
`ConcurrentReplay.run_view` projects those actual steps onto the same scalar
instructions used by the local contraction proof. It retains the thread's
registers, instruction position and allocation bounds. For interpreting loads,
it uses a **byte view**: a function giving the input byte at each address.
The view is not taken from the candidate machine's possibly stale local memory.
Every recorded read in the interval must first be proved equal to the eight
bytes in this view. No numerical answer is assumed.

Three facts make this projection sound:

1. Each fetched instruction in the interval is the same store-free data
   instruction as in the scalar program. Stores and branches cannot be silently
   dropped.
2. Other threads' ordinary steps leave this thread's registers unchanged.
   A barrier cannot advance it while its next instruction is an arithmetic or
   memory instruction: a valid release requires all participants at the same
   barrier.
3. Arithmetic uses the actual permitted rounded result. Replay does not
   reassociate sums or restrict NaN payloads beyond the original contracts.

`ConcurrentReplay.contraction` then obtains the pinned TorchLean matrix-product
coordinate from the actual concurrent run. `ConcurrentComputedStore.stored_contraction`
continues through the two address instructions and inspects the real store
event. Its decoded stored word equals that coordinate. The publication theorem
can transport this result to a later thread's load once it identifies the
producer. Stored bits and decoded floating-point equality remain distinct.

### Justifying the first inputs

For the concrete certified Q1–Q4 middle programs, `CellMiddleInputs` proves that
all executed stores are shared stores in planes 1–6. In particular:

- global coefficients have no writer in the slice;
- no store overlaps even one byte of input plane zero;
- under byte-source compatibility, reads within those regions must recover
  their initial bytes. The proof does not require whole-word atomicity or a
  sequential schedule.

Here “initial” means the storage at the start of this middle slice. The omitted
gather still has to establish how those bytes represent the input tensor.

### Completing the numerical connection

The concrete theorem is `CellMiddleCorrespondence.completed_middle`. It covers
a complete run of the three middle phases, for widths 2–5. Its companion
`completed_store` identifies the actual store event for every output coordinate.
The conclusion is decoded floating-point equality to TorchLean, including its
order of operations. It is not a real-arithmetic identity or a claim that all
NaN bit patterns agree.

Let B be the interpolation table, D the derivative table, W the integration
weights, and U the shared input matrix. The six proved planes are:

| Plane | TorchLean calculation |
| --- | --- |
| 1 | BU |
| 2 | DU |
| 3 | W multiplied entry by entry with (BU)Dᵀ |
| 4 | W multiplied entry by entry with (DU)Bᵀ |
| 5 | Bᵀ times plane 3 |
| 6 | Dᵀ times plane 4 |

Each matrix product is an increasing-index fold starting at positive zero,
with separate rounded multiplication and addition. The proof exchanges only
the two operands of a single weight multiplication; it never rearranges a sum.

The proof connects the actual instructions in four steps:

1. **Find the reads.** `Symbolic` records address expressions in registers.
   Its address mode deliberately forgets loaded values and floating-point
   results. `CellLaunch.load_location` therefore derives each load's address
   without assuming that its value is right. Finite kernel-checked certificates
   establish which initial region or intermediate plane contains that address,
   and which barrier must precede a read of an intermediate plane.
2. **Justify their values.** `CellWordView` reads initial coefficient/input bytes
   and looks up actual output stores. `CellReadValues.all_reads` proves that every
   actual load equals this view, using read-only inputs or the previously proved
   unique producer and barrier visibility. A required producer is proved to
   exist; the lookup's default value never substitutes for a missing store.
3. **Follow the arithmetic.** The value mode records the ordered floating-point
   expression, and `SymbolicRun` proves it agrees with actual registers across
   arbitrary thread interleavings. `CellSymbolic` checks the exact matrix
   coordinates and operations at all six store sites. The checks cover every
   active lane in each Q1–Q4 program, not an enumeration of input values.
4. **Compose the tensors.** `CellTensor` connects each expression to TorchLean's
   matrix-product fold. `CellMiddleCorrespondence` substitutes the six plane
   equations and proves that their values are emitted by actual stores.

The launch conditions say exactly what must hold at this slice's entry: all
32 threads start at its first instruction with a reset barrier, correct base,
lane and row/column registers, and a nonwrapping seven-plane shared allocation.
The executed instruction relation supplies each access's validity. The theorem
requires a completed run and the two necessary byte-source constraints,
`Compatible` and `Performed`. It assumes no read values, phase answers, supplied
scalar traces, store coverage or producer-ordering paths.

This finishes numerical correspondence for the **middle slice**. The complete
cell still needs its prologue, gathered-input connection, final contractions,
addition and global output joined to this result. The proof does not establish
full PTX memory admission, arbitrary-input execution existence, GPU progress,
or whole-solver correspondence.

`ConcurrentReplayChecks` provides a nonzero example: two threads alternate
instructions while each computes a one-term contraction of 2 and 3. Compatible
load sources justify the byte view; the generic theorem identifies the actual
store of 6 with TorchLean's result. The fixture deliberately gives the candidate
lanes different local bytes, so correctness cannot come from accidentally
reading those local snapshots. A negative example rejects a fabricated read
from the read-only input. This is a test of the reusable proof interface, not
a replacement for Q1–Q4 numerical composition or a hardware experiment.
