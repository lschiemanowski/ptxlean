# Reduction integration review

This review distinguishes actual instruction execution, candidate memory
constraints, execution existence and PTX source fidelity. The pinned-source
review is `trace-memory-source-review.md`; the specialized guides and dependency
reports remain separate evidence. The coordinator inspected the definitions and
proof interfaces below independently of their implementing agents.

## Actual program and initial state

The fixed program contains its global loads, computed byte addresses, shared
stores, full barrier, leader selection, explicit register initialization, loop,
output store and exits. Cross-block transitions are fetched branches. Only a
completed barrier changes all lanes' continuation labels. The control invariant
establishes that every resumed lane was actually waiting at that site; no
unrelated lane can be advanced by a fictitious completion.

The only supplied register binding is the lane identity in the starting state.
All other banks, the old output and all scratch contents are arbitrary. Actual
move instructions initialize the leader's accumulator, counter and pointer.
The program returns a modular u32 sum, not an unbounded integer sum. It leaves
extra global and shared words unchanged in the constructed complete execution.

The scalar memory field is an evaluator view of the selected persistent arena.
It is not an independent source of initialized words. Reads use that arena or a
candidate override after address checking; actual returned memory supplies
writes. No model field installs the desired publication vector or final sum.

## Execution history and values

History counters prove that each thread publishes at most once and that the
single barrier completion follows all participants' arrivals. Arrivals follow
actual stores. Exact-index prefix extraction locates the specified read in the
complete trace, including nonmemory events and blocked dispatches. A membership
proof about an equal event at another index would be insufficient; the final
indexed theorem avoids that ambiguity.

The data invariant derives each producer address from its supplied lane identity
through the executed conversion and doubling instructions. The value invariant
records an actual earlier global load whose value survives into the shared-store
register. Neither invariant assumes that a load is fresh or equal to an input.
Those are obligations discharged by the separate memory graph.

## One combined memory graph

The graph fixes its labels from the actual trace and the original global/shared
contents. Space identity distinguishes equal offsets in the two allocations.
Projection checks instruction fetch, execution, memory kind and exact effect;
completeness excludes disappearing accesses. Source and write-order parameters
cannot alter those labels. Barrier order uses actual same-key arrivals and
completion, with each endpoint on its own participant's side of the barrier.

The initial-source theorem excludes the final output store as a source of input
loads because its computed address is the separate word `n`. For shared reads,
actual history, per-thread publication uniqueness and computed-slot identity
are separate prerequisites proved by the control/data layers. They must not be
replaced by a premise that the desired write supplies the read.

## Constructive witness

`canonical_valid_exists` builds read sources and write ordering for the actual
complete schedule. It derives the exact access classes from `full_accesses` and
uses a strictly increasing rank for actual dynamic accesses. Initial events
precede program accesses. Each read has a matching preceding write, and all
competing same-location writes are bounded by that source. These facts discharge
`SerialCertificate`; no valid graph, desired read, source choice or final result
is assumed by the existence theorem.

The same certificate proves that the chosen execution has no cycle of base-order
and read-source edges. This is a sufficient grounding argument for this witness,
not a proposed full no-thin-air rule. The universal candidate result must not be
restricted to this serial schedule or strengthened with the witness's rank.

## Safety and distinguishing examples

The independent safety review in `shared-reduction-safety-review.md` checked the
coordinator-authored safety module. Both arena lengths are invariant. Every
emitted memory effect has passed the scalar evaluator's alignment and bounds
checks in its actual selected arena, including overridden candidate loads.
Safety of emitted effects does not assert absence of faults or termination.

`SharedReductionExamples` separately checks a wrapping sum, preserved scratch
tail, 32- and 64-lane instances, an incomplete barrier whose repeated waiting
lane cannot manufacture completion, a wrong global read rejected by source
compatibility, and an actual fully terminating stale shared-read execution that
writes 96 instead of 8 and is rejected by the combined memory constraints. These are selected distinguishing checks, not GPU experiments.

## Source boundary

This fragment represents one isolated cooperating thread array (CTA), full-word
aligned ordinary generic-proxy memory operations, one complete barrier phase,
initialized allocations and no external interference. The runner itself is
target-neutral; ISA 9.4/SM feature eligibility is a separate qualification.
Physical allocation mapping, ownership, launch geometry, lane identity and
hardware barrier correspondence remain explicit source-level obligations.
A finite execution witness does not establish fairness or general GPU progress.
The graph conditions remain necessary constraints, not complete PTX admission
for arbitrary programs with dependent values, addresses and control flow.

## Final public composition

The loop invariants derive the actual leader's cursor and remaining count from
executed initialization and updates. The accumulator invariant follows the
intermediate instruction positions, including the loaded-but-not-yet-added word
and the advanced-pointer-before-counter-decrement case. The memory layer forces
the value at each actual shared-read address; it does not assert an aggregate
sum. Arithmetic then derives the modular sum and actual output effect.

`Correctness.read_contract` discharges the arithmetic helper's observation
premise from `Graph.Ordered.Valid` on the full combined trace. Neither
`candidate_output` nor `completed_candidate` exposes an expected-read, source
identity, unique-writer, freshness, arithmetic-invariant or final-state premise.
The latter requires the actual leader to have halted; control proves this occurs
after its output store. Persistent writeback then proves the entire final global
list equals the original list with only word `n` replaced by the sum.

This is universal conditional correctness under the selected necessary memory
constraints. It is not a claim that those constraints completely characterize
PTX. The canonical witness separately discharges validity and grounding;
no serial-schedule restriction is added to the universal theorem.
