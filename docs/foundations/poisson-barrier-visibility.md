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

The saved-PTX checker also verifies the five-phase control skeleton of each
Poisson element entry: five matching guards and labels, four unpredicated
`bar.sync 0` boundaries, the expected lane predicate, no internal control transfer
or predicate modification in the bodies, and the final return. Mutation tests
reject a skipped, moved, predicated, or renumbered barrier. This is a syntactic
frontend check, separate from the Lean theorems.

The full generated cell kernel is **not yet proved**. It remains necessary to
connect its prologue and every phase body to this concurrent machine; derive the
store/arrival/completion/read paths and single-writer coverage for all its
permitted executions; and join those events to the local contraction/store
proofs. Gather, weighting, final addition/output, and whole-solver composition
also remain open. The reusable visibility theorem must not be mistaken for a
completed proof of those instantiations.

Run the checked proofs and regression tests from the repository root:

```sh
integration/torchlean/check.sh
python3 -m unittest discover -s hardware -p 'test_*.py'
```

The saved-artifact binding check is described in
[the cell contraction guide](poisson-cell-contractions.md).
