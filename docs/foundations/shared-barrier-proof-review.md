# Independent proof review of the shared barrier fragment

The review found no blocking issue in the checked source snapshot below. It
examined definitions, theorem statements and proof dependencies, rather than
using compilation as a substitute for checking what was proved. The independent
[source review](shared-barrier-source-review.md) supplies the separate argument
for interpreting this restricted model against the pinned PTX 9.4 clauses.
Neither review is a formal proof of NVIDIA hardware conformance.

## Instruction and execution origin

`SharedBarrierMachine` fetches a fixed four-instruction program: an explicit
relaxed CTA-scoped shared store, `bar.sync 0`, an explicit relaxed CTA-scoped
shared load, and exit. The event fields come from that dispatch: thread, program
counter, shared byte address, store input, and selected load value. Its encoder
and decoder use typed tokens; their roundtrip theorem does not establish a raw
PTX text parser or coverage of other instruction forms.

`SharedBarrierProgram` initializes the selected registers and addresses from
supplied data. The remaining registers, old arena contents and initial inputs
are arbitrary. A checked address bound prevents truncation of `4*i` to the
32-bit shared offset. Its canonical schedule really executes four stages of
`n` instructions, producing `4*n+1` events: stores, arrivals, one completion,
loads and exits. The extra event is the completion emitted together with the
last arrival.

Proposed-read execution leaves each thread's proposed observation arbitrary.
Concrete execution instead loads its arena. The canonical execution theorem
covers both modes without treating a proposed observation as a valid PTX read.
The selected concrete execution agrees with the candidate whose observations
are the freshly stored words; this gives a witness, not universal visibility.

## Reachability justifies release

`SharedBarrierInvariant.Control` is established from initially live threads at
program counter zero and an initial barrier. Before completion every thread is
at zero or one; after completion every thread is at two or three. Arrived
threads are parked at one. Therefore, when the final arrival fills the arrival
set, every participant is at the common site. This derives the condition needed
for the machine's group-wide advance; the condition is not inserted as a new
release hypothesis.

The invariant holds for arbitrary finite schedules, including retries and
failed access checks, and for arbitrary proposed read values. Program counters
never move backwards. Event-count balances show that reaching generation one
from the initial barrier emits exactly one completion and one arrival per
participant. Store and load counts are tied to actual successful instructions,
not inferred from a convenient memory result.

The prefix theorems identify actual earlier schedule segments: each arrival has
its own store before it, each completion has every participant's store before
it, and each load has completion and every arrival before it. All emitted keys
are the configured CTA, resource zero, generation zero and site one. Halted
status is distinguished from merely reaching PC three and is connected to an
actual exit event. These claims neither assume fairness nor establish general
barrier reuse, divergence or early-exit semantics.

## Data, memory and allocation obligations

`SharedBarrierFrame` preserves the input register, all shared-address registers
and the arena owner for every schedule. Consequently the actual store and load
events have the initialized own-slot and partner-slot addresses. Its `Output`
invariant relates the result register to the proposed observation only. It is
proved from the initially vacuous PC condition and instruction behavior; it does
not assume the observation equals the desired partner input.

`SharedBarrierMemory` has exactly three events per slot: initialization, one
program store, and the owning thread's partner load. Proposed read values, read
sources and coherence ordering remain parameters. Source compatibility narrows
a read to the selected location's initialization or its program store. Initial
writes precede program writes in coherence; added barrier causality and the
no-stale-read condition exclude the initial source. Only then does source
compatibility establish value equality.

The fresh validity witness discharges all memory-certificate fields, including
coherence and per-location acyclicity. The old-source witness without barrier
order excludes self-partners because their own program order already constrains
the read. Adding barrier order rejects the old source even when initial and
newly written values happen to be equal. Thus the negative result concerns
source identity, not only unequal words. Both validity witnesses are nonvacuous
mathematical graphs, separately from instruction-execution existence.

The coarse phase levels produce exactly store-to-load edges and exclude
initialization. They are dependency ranks, not global timestamps. The selected
64-thread example uses two groups of 32 lanes and proves its partner lies in the
other group; it makes no universal claim about a machine's warp size.

`SharedBarrierEnvironment` derives acceptance by the ordinary allocation checker
from actual emitted accesses. Four-byte alignment and an in-range word index
imply complete byte bounds in the `4*n` arena. The coupling's `trace_accessible`
extends this to every event of every finite run, against the same initial
allocation descriptor. Initialized contents are supplied arbitrary words, not
zero filling. This internal arena model does not certify external allocation,
launch admissibility, or absence of other cluster participants.

## Coupling checked in this snapshot

The main module's canonical projection accounts for every program memory event,
and initial graph labels match the supplied initial arena. Its ordered trace
sublist contains the store, producer arrival, common completion and consumer
load. It obtains universal proposed-value correctness conditional on full graph
validity; it does not replace validity by a selected source relation.

`verified_execution` combines an actual finite concrete execution, halted result
registers, final arena, completed barrier state, a fully valid fresh-source graph,
exact projected labels and access checking. The 64-thread corollary instantiates
that program with the cross-warp partner map.

The final main coupling also covers arbitrary completed dispatch schedules.
`completed_candidate_publication` requires only that the actual final threads
have halted, in addition to the explicitly stated full graph validity. It derives
the partner values through the proven result-observation invariant and includes
exactly one actual store and load per thread. Completion is a conditional premise
here; the separate canonical witness supplies nonvacuous finite existence.

`SharedBarrierHistory` connects counters to actual event membership and ordered
trace sublists. In particular, `completion_path` handles both the final arriving
writer and an earlier arriving writer: the final arrival precedes completion
within their shared step, whereas earlier arrivals occur in the earlier trace.
`load_path_general` supports both concrete and proposed-read modes. It derives
every producer's store–arrival–completion–load path from an actual load event,
without a memory-validity or expected-value premise.

`completed_cross_origin` finds the actual reader event from the exact load count,
uses the history theorem, and identifies its fields through the frame theorem.
Thus every additional memory-order edge has the required common-key trace path
for every completed candidate schedule. `completed_memory_accounting` separately
ensures exactly one store and load per participant, with every memory event
having one of their exact field patterns. The canonical trace equality remains
a stronger convenient identity for the constructed witness, not an assumption
imposed on other scheduling interleavings.

`all_in_scope` proves mutual CTA scope from the supplied one-CTA topology;
`observation_scope` then proves agreement with the existing scoped-observation
rule. Initialization does not acquire a fictitious participant identity.

## Verification record

All eight listed modules were built explicitly. The 144 public theorem declarations
were audited with temporary import drivers that printed
`#print axioms` for every public theorem declaration. The checked endpoints use
only `propext`, `Classical.choice` and `Quot.sound`. No `sorryAx`, new unchecked
axiom or `native_decide` trust extension occurred in those dependency reports.

| Module | Public theorems | Reviewed SHA-256 |
| --- | ---: | --- |
| `SharedBarrierMachine` | 11 | `f8e6b3ba9faf7a38c7ceee46da5db06c24193471511e2733806cad2dc84792bc` |
| `SharedBarrierProgram` | 32 | `6538ae756c5f4c5d08c214533994ff8dcc717e18098239c89f1088a26926ceca` |
| `SharedBarrierInvariant` | 34 | `0bfe96786159520448ceb3692202ef63459c3bfa2afa31c90e20eec3e45671a9` |
| `SharedBarrierFrame` | 16 | `64c85c7e16ae899caa05ea9ddeddef731734dd8c059c77d2f8828059fe583b57` |
| `SharedBarrierMemory` | 20 | `af8d79de615ec1e7957c3e7ef2fce30011bfed8bae9d07e1e1acac092be1bc6f` |
| `SharedBarrierEnvironment` | 3 | `9b99c81224a769357f1c005002bb2073fdc7adc03dd8bd62b1f89e4be777d316` |
| `SharedBarrierHistory` | 12 | `9e8350236ff861e3e329ad46e1f23261aecd130cf216919d3b072e1b4f9f36c0` |
| `SharedBarrier` | 16 | `bdc75fc333e9b11469f5f50e32000df762a68cf8b899cc31caba2f92be107de3` |

The implementation scope is a closed, uniform, full-participation shared window
with aligned whole-word accesses and no competing external writes. Reuse of the
word-level graph requires the source review's explicit scope, proxy, overlap and
single-copy argument. It does not follow from alignment alone, nor from merely
renaming an originally global-memory theorem.
