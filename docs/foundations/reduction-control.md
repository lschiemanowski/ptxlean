# Why releasing the reduction barrier does not skip work

The reduction machine has one fixed instruction program. Each thread computes
its input byte address, loads its global word, writes a shared slot, and reaches
the common barrier. After the barrier, a fetched comparison chooses the leader;
fetched moves initialize its counter, sum and pointer. The leader then executes
the load/add loop and output store. The control proofs in
`Ptx/SharedReductionControl.lean` concern actual steps of that machine.

The barrier protocol itself only records arrivals. It does not know whether a
thread reached an instruction. `Control.Invariant` supplies that connection:
whenever the protocol says a thread has arrived, the actual thread is live and
its block/program-counter pair is `(barrier, 0)`. This deliberately weak invariant
does not assert input values, a desired result, or memory freshness.

`initial` establishes the invariant from the supplied program start, and
`step_preserves` proves it for every actual dispatch, including arbitrary
candidate load values. `runWith_preserves` lifts that proof over any finite
schedule. There is no chosen-order or fairness premise.

A waiting thread cannot advance itself: `waiting_step_unchanged` proves that
rescheduling it returns the same state, a waiting status and no new events.
For a release, `release_all_at_barrier` combines actual fetch with the protocol's
all-participants condition. Previously marked participants are at the site by
the invariant; the final participant is there by its fetched `sync` instruction.
Thus moving all lanes to the continuation does not skip an unarrived thread's
producer work. `reachable_release` derives the invariant from initialization and
an arbitrary preceding execution, rather than asking the caller to assume it.

## Following an actual memory event

The machine's instruction type distinguishes local instructions from memory
instructions labelled global or shared. That wrapper alone permits more syntax
than this one fixed program uses. `fetched_classification` proves that every
actual fetched local instruction has a nonmemory opcode, and every fetched
memory instruction really has a load/store opcode. Its conclusion is explicitly
about the fixed program, not unrestricted calls to `dispatch`.

`runWith_memory_origin` proves that any scalar event carrying a memory effect
has a concrete space label, the exact fetched `.memory` instruction at the
event's original PC, an executed guard, and a matching load/store kind. This
holds for arbitrary starting states, schedules and candidate reads. A memory
projection therefore cannot excuse a missing effect as an unlabelled local
instruction. The separate adapter still proves its own index/count/order
properties; a repeated PC in the loop is not a unique occurrence identity.

`runWith_global_store_address` goes further: every actual global store has byte
address `4*n`, the immediate operand in the fetched output instruction. This
fact does not depend on initial register contents or candidate reads. The
input-address range is below that slot, so the memory adapter can use it to
exclude program stores as input-read sources. Source compatibility and output
correctness are still separate results.

## Source qualification and limitations

The machine is target-neutral. `SupportedTarget` restricts the PTX interpretation
to ISA9.4 and the numeric feature condition `sm >= 70`. `forms_eligible` proves
that the selected relaxed GPU-scope global and relaxed CTA-scope shared load/store
forms pass the existing environment eligibility checker. It does not validate
all textual architecture names, suffixes, launch geometry, or assembler support.

The pinned PTX9.4 source is
`references/nvidia/ptx-isa-9.4/index.html`, SHA256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
Relevant exact anchors are:

- §9.7.15.1 `parallel-synchronization-and-communication-instructions-bar`:
  full-CTA participation when count is omitted, aligned common-site execution,
  completion/resumption/reset, and ordering of memory accesses. The current
  control proof establishes waiting-site consistency, not memory visibility.
- §9.7.10.8 `data-movement-and-conversion-instructions-ld` and §9.7.10.11
  `data-movement-and-conversion-instructions-st`: explicit relaxed/scope support
  requires PTX6.0 and sm70. No default weak opcode is promoted to relaxed by a
  proof; the memory wrapper is interpreted as those selected explicit forms.
- §6.4.1 `addresses-as-operands`: addresses are byte-based and naturally aligned;
  32-bit and 64-bit carriers are allowed, with truncation to state-space width
  where necessary. The reduction's separate no-wrap/address proofs must establish
  its actual shared offsets fit below 2^32; this control module does not prove
  all address bounds merely by using a 64-bit register carrier.
- §8.3 `memory-consistency-state-spaces` and §8.9.1 `program-order`: state-space
  tags do not justify discarding cross-space ordering, and repeated dynamic
  occurrences must remain distinguishable from repeated PCs.

All participants are the complete represented CTA, with no pre-barrier exit and
one common barrier site. Individual arrival bookkeeping is still a specialization,
not a general refinement of PTX warp arrival dynamics. The no-interference,
allocation ownership, source-compatibility and memory-order conditions remain
outside these control conclusions. The staged block proofs in SharedReduction
are not themselves a whole-program theorem; the separate SharedReductionProgram
composition must supply that claim using actual fetched transitions.

## Verification and review responsibility

`lake build Ptx.SharedReductionControl` and a fresh `lake env lean` dependency
audit checked all public declarations. Only `propext` and `Quot.sound` appeared;
there are no new unchecked axioms, `sorry`, or `native_decide`. The public-name
list and full audit are recorded separately for the coordinator.

This work began as an independent semantic review of SharedReduction and
SharedReductionMachine. The early review identified the missing arbitrary-schedule
waiting invariant, fetched opcode classification and target qualification. The
reviewer then became the author of these separate control proofs at the
coordinator's request. Final independent review of this module therefore belongs
to another reviewer; this document is not a claim of self-independent approval.
