# From independent lanes to one shared allocation

This study proves integer vector addition for arbitrarily many lanes operating
on one memory list. Every scheduler action executes one load, load, add, store,
or exit instruction. The proof no longer treats a lane's whole computation as
an indivisible action or assumes each lane has a private memory copy.

Start with the [verification rules](scalar-rules.md), then open
[`SharedVector`](../../Ptx/SharedVector.lean) and
[`SharedVectorMemory`](../../Ptx/SharedVectorMemory.lean). The
[independent source review](next-source-review.md) separates these checked
results from their restricted relationship to PTX.

## The contract and layout

Lane `i` owns the following three consecutive words in the single allocation:

| Word index | Responsibility |
| --- | --- |
| `3*i` | Read-only left input |
| `3*i+1` | Read-only right input |
| `3*i+2` | Output, written only by lane `i` |

Each instruction uses the corresponding byte address, four times its word
index. This interleaved layout is the simplest example of an injective ownership
mapping; it is not proposed as an optimized tensor layout. All memory operations
use the scalar subset's relaxed GPU/global form and generic proxy. Initial
memory and all 32-bit registers are supplied inputs. Auxiliary address registers
and predicates are irrelevant to this instruction list, and the scalar-step
correspondence allows arbitrary values for them.

For `n` lanes the execution-level theorems require `3*n ≤ memory.length` and
`12*n < 2^64`. The first covers every actual access; the second ensures the
natural-number layout is faithfully represented by the 64-bit pointers. These
are sufficient bounds, not a characterization of every legal GPU allocation.
Words beyond the footprint remain available and are proved unchanged.

## Why interleaving is harmless here

`State` has one `memory` field, plus each lane's register file and cursor.
`advance` schedules exactly one instruction. Cursors 0 through 4 designate the
five instructions; cursor 5 records that the explicit exit has run. Scheduling
an already completed lane stutters. No load reads from a private snapshot:
it reads the shared memory at that step.

`Invariant` records unchanged original input words, the values loaded into the
two operand registers, the computed sum, and the output after its store. These
facts are established incrementally. They are not preconditions asserting the
kernel's desired final result. `output_ne_left`, `output_ne_right`, and
`output_injective` discharge the interference argument: every store misses all
input words and every other lane's output.

`advance_invariant` proves one-step preservation; `execute_invariant` lifts it
to arbitrary finite schedules. `completed_correct` derives every final output
from that invariant. This theorem concerns the mathematical `advance` machine.
`advance_is_scalar_step` and `execute_faithful` additionally use allocation and
pointer bounds to establish the connection to actual scalar instructions,
including register-computed store operands and the executed exit.

`execute_frame` preserves every non-output word, including any trailing memory.
`trace_access_safe` establishes aligned complete accesses for every emitted
memory label, including schedules that have not completed. Safety of such a
prefix does not imply termination.

## Existence and scheduling

`schedule n` visits all lanes five times. `execute_cursor` relates each final
cursor to the number of times that lane was scheduled. `schedule_complete`
and `completed_execution_exists` construct an actual completed execution with
exactly `5*n` dispatches, the correct outputs, and the memory frame.

This is an existence theorem. An unfair schedule can ignore a lane forever.
The example `unfair_schedule_incomplete` checks that repeatedly scheduling only
one of two lanes does not finish the other. No hardware fairness or progress
claim is hidden in the schedule construction. The empty-lane case is permitted
and completes without dispatches.

[`SharedVectorExamples`](../../Ptx/SharedVectorExamples.lean) checks two different
instruction interleavings over the same allocation, a modular-overflow case,
untouched trailing memory, and rejection of an empty arena at the actual scalar
execution boundary. It also uses the generic segment and frame rules to prove
a small completed instruction sequence without re-proving its full execution.

## The relational connection

`emitted` extracts each memory label from the effect justified by scalar
stepping. `trace_correspondence` is a telescoping argument: emitted labels plus
the labels still to be emitted equal the original per-lane sequence.
`completed_trace` therefore derives exactly two loads and one register store
for each lane, with positions 0, 1, and 3, for every completed interleaving.
Filtering by thread retains local order and introduces no cross-thread ordering.

`SharedVectorMemory.witness` builds a graph for arbitrary `n`, with three
initialization events and those three memory events per lane. `witness_valid`
proves every field of the unchanged restricted `Graph.Valid`. Read sources are
the input initialization writes; coherence relates each output's initial write
to its program store. The graph contains the accessed footprint, not unused
initialization events for a trailing allocation region. `initial_labels`
connects every included initialization value to a real in-bounds allocation cell.

`shared_trace_labels` identifies the graph's three program events with each
lane's **actual shared-execution trace**. The central
`verified_shared_execution` theorem packages the completed instruction execution,
outputs, graph validity and trace correspondence. This prevents presenting a
correct interpreter run and an unrelated valid graph as an end-to-end result.

There is also a separate universal relational statement. `input_sources` proves
that every source-compatible candidate graph must choose the original input
values, across all lanes and arbitrary coherence choices. `candidate_output`
then derives the correct register-store value. Input/output separation supplies
a concrete grounding argument; it does not solve general dependent concurrent
no-thin-air semantics. The candidate graph family fixes this kernel's memory
event structure, so it is not a general characterization of all PTX executions.

## Review and reproduce

The reusable scalar rules distinguish exact exhausted segments, completed runs,
partial correctness, and total correctness. Their frame theorem quantifies over
actual emitted stores; their termination rule requires local progress and a
decreasing natural measure. Neither assumes the completed result it should prove.

Run `./scripts/check.sh --clean` to rebuild and audit the public results. For
review, read `verified_shared_execution`, its trace link, and the invariant
before inspecting the supporting proofs. Remaining boundaries include the
layout-to-runtime allocation mapping, launch/module ABI, hardware conformance,
and general PTX dependency semantics. No floating point, TorchLean integration,
async instruction, or application-level network code is introduced here.
