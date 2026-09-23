# Source review: a first CTA barrier and shared-memory reduction

This independent review fixes source obligations before implementing barrier
execution. A CTA (cooperative thread array) is the group of threads launched as
one thread block. A warp is a smaller execution group within that block. Neither
term means that the formal scheduler may assume all those threads advance at once.

The normative input is the [pinned PTX ISA 9.4 manual][manual], SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
`python3 scripts/check_sources.py` verified that artifact. The source passages
below were read in full where indicated. This document is a source interpretation,
not a proof of hardware correspondence or a completed barrier implementation.

## Smallest useful first form

Start with **`bar.sync 0;`**, with an immediate barrier number and no explicit
thread count. It is equivalent to `barrier.sync.aligned 0;`. Support one CTA,
full participation, no early exits, and a common unconditionally reached barrier
instruction. Start with synchronous, aligned, distinct `.u32` shared-memory
accesses through the generic proxy (the ordinary memory access mechanism).
Use explicit `st.relaxed.cta.shared.u32` and `ld.relaxed.cta.shared.u32` forms if
we want to reuse strong-operation memory rules; bare `st.shared`/`ld.shared`
default to weak accesses and must not silently acquire relaxed semantics.

A useful concrete reduction has two complete warps. Under a target configuration
with warp size 32 this is 64 threads: each writes its input to a separate shared
word, all execute the barrier, and one designated thread reads the words and
sums them with 32-bit wrapping arithmetic. The remaining threads may exit after
the barrier. The barrier itself does not calculate the sum; this example does
not require the distinct `bar.red` instruction family. The warp-size assumption
must be recorded; the general [CTA description][cta] describes `WARP_SZ` as a
machine-dependent constant rather than a universal mathematical 32.

This is a small semantic slice, not the whole barrier family. No count operands,
register-selected barrier numbers, `.arrive`, `.red`, warp barriers, cluster
barriers, asynchronous completion or divergent barrier participation should
silently enter its coverage claim. A first model can support only one resource,
number 0, while its state representation retains resource and reuse identity.

## Source clauses and concrete obligations

The complete [bar/barrier instruction section][bar] is §9.7.15.1, HTML lines
24525–24681. Its requirements are more substantial than pausing at an annotation.

| Subject | Manual rule | Obligation for the first slice |
| --- | --- | --- |
| Resource identity | Each CTA instance has sixteen resources numbered 0 through 15. The number operand is `.u32`, immediate or register. | Resource 0 belongs to the particular CTA instance, not a global barrier named 0. Other numbers are unsupported by this slice, not illegal PTX when in range. |
| Participation | Omitting the count selects all CTA threads. An explicit count must be a multiple of warp size; `.arrive` requires a nonzero count. | Fix the launch's finite participant set. Do not infer participants from whichever threads happen to have arrived. Reject count-bearing forms until their contract is implemented. |
| Warp arrival | An executing thread waits for all non-exited threads of its warp, and the warp's arrival is marked. | Record individual arrivals and distinguish a complete warp arrival. A simpler all-thread arrival set is acceptable only with a proved specialization for the full-CTA/no-exit slice. |
| Blocking | `.sync` additionally waits for non-exited threads of every participating warp. `.arrive` does not wait for the other warps. | A waiting thread cannot execute the instruction after the barrier. Scheduling it again must not register a duplicate arrival. |
| Completion and reuse | Completion restarts waiting threads and reinitializes the barrier for immediate reuse. | Distinguish successive uses of the resource, for example with a generation number. Clear arrival state on completion; a previous generation's arrivals cannot complete the next one. |
| Alignment | `.aligned` promises that all CTA threads execute the same barrier instruction. In conditional code they must evaluate the condition identically; otherwise behavior is undefined. `bar.sync` implies `.aligned`. | Use a common unpredicated barrier site and prove every participating thread reaches it. This alignment concerns collective control flow, not byte-address alignment. |
| Mixing forms | Warps may mix `.sync` and `.arrive` with the same name/count subject to the described reuse discipline. Mixing `.red` with `.sync`/`.arrive` on an active resource is unpredictable. | Do not assign ordinary defined outcomes to excluded combinations. Implement only `.sync` in the first slice. |
| `.cta` spelling | Optional `.cta` makes the applicability explicit without changing the semantics. | Do not conflate spelling aliases with support for cluster barriers. Record which spellings are actually decoded. |

The [exit section][exit] (§9.7.14.7, lines 24466–24490) states that barriers waiting
only for exited threads are released. Consequently, a future general barrier
cannot forever require an arrival from every thread that existed at launch.
Conversely, this rule does not establish arbitrary visibility of an exited
thread's memory operations or exempt unrelated threads from the barrier.
The first slice excludes exits before the barrier and proves that condition from
the program. Exits after its final barrier remain ordinary completed thread
execution. Reporting that limited coverage is essential; a static participant
count alone is not full exit-aware PTX barrier semantics.

[Independent thread scheduling][scheduling] (§3.2, lines 1669–1691) rules out
assuming that same-warp threads communicate correctly without synchronization.
[Control divergence][divergence] (§9.5, lines 8840–8856) explains divergent versus
uniform control. The barrier-specific restrictions still govern; a general
statement about reconvergence does not license an aligned barrier on paths taken
by only some threads.

## Version and target conditions

Keep instruction availability distinct from the narrower target choice used by
the formal memory interpretation.

| Feature | PTX ISA minimum | Target requirement in the instruction section |
| --- | --- | --- |
| `bar.sync` with immediate resource, no count | 1.0 | This is the supported barrier form on `sm_1x`; later forms have additional restrictions below. |
| Register operands, explicit count, `bar.arrive`, `bar.red` | 2.0 | `sm_20` or newer. |
| `barrier` spelling, including `.sync.aligned` | 6.0 | `sm_30` or newer. |
| Explicit `.cta` qualifier | 7.8 | No additional target threshold stated for the qualifier itself. |
| The proposed explicit relaxed shared-memory accesses | 6.0 | `sm_70` or newer, from the [load][ld] and [store][st] sections. |

For `sm_6x` and earlier, the barrier section equates the unaligned spelling to
its aligned variant and additionally requires non-exited warp threads to execute
in convergence. Do not apply modern independent-thread reasoning unchanged to
those targets. For the first reduction, pin PTX 9.4 and `sm_70` or newer; [§8.1][scope]
also limits the documented memory consistency model to that target range. This
modern-target restriction is a project slice, not a claim that `bar.sync` first
became available on `sm_70`.

## The ordering a barrier must actually provide

The instruction description supplies two guarantees:

- At completion, a participating thread's earlier memory accesses have been
  performed relative to the other participants. Earlier reads have their fixed
  values; earlier writes are visible so their predecessors cannot still be read.
- A `.sync` thread does not request a new memory access before completion.

[§8.9.4, Memory synchronization][synchronization] relates an arrival/synchronizing
barrier operation to the corresponding synchronizing operations of other threads
on that barrier. [§8.9.1, Program order][po] and [§8.9.5, Causality order][cause]
then connect an earlier store in one thread to a later load in another. For
matching addresses with the generic proxy, that base path gives the causality
used by [§8.10.6][causality-axiom] to prohibit reading an obsolete write.
For a scratch word with exactly one program writer, after the common barrier
a read must obtain that writer's value rather than the old initial value. Prove
source identity and then value agreement; do not assume the desired sum or that
the read already obtained the published value.

The memory effects are relative to participants and accessible storage. A CTA
barrier does not synchronize other CTAs merely because they reuse its number.
[Shared storage][shared] is owned by a CTA; this slice uses only its own `.shared`
window and excludes peer-CTA cluster access. [§8.3][spaces] separates memory-order
relations from storage accessibility. Bounds, initialization, access permission
and allocation lifetime remain separate checks.

There is an important representation trap. If one adds bidirectional
synchronization edges between *single* barrier nodes directly to the current
acyclic base-order graph, a collective barrier produces a false cycle. A sound
foundation needs distinct arrival and completion/resumption roles, or a justified
projection that derives only pre-barrier-to-post-barrier memory ordering.
For example, each arrival can feed a common completed-phase event, which precedes
all resumed participants. This is a proposed formal representation, not extra
PTX syntax. Its connection to actual execution and source ordering must be proved.
Do not instead weaken the existing acyclicity condition simply to accept a cycle.

The source's phrase “same barrier” must also be interpreted together with resource
reset: resource number alone cannot identify all dynamic synchronization partners
across arbitrary reuse. Track CTA identity, resource number and generation, and
justify the ordering between successive uses. Do not connect all occurrences of
`bar.sync 0` indiscriminately.

[§8.9.1.1][async-po] explicitly treats asynchronous operations differently from
ordinary program order. This review does not infer that `bar.sync` waits for all
previously issued asynchronous instructions. Their documented completion
mechanisms must be modeled separately.

## What the executable foundations still lack

Inspection of `Scalar`, `Scalar.Ordered`, `SharedVector`, `Environment`, and the
whole-word graph establishes the following missing pieces:

1. **Collective execution state.** `Scalar.State` contains one thread's PC,
   registers and memory list. Its stop states do not represent waiting at a
   barrier. Add runnable/waiting/exited distinctions, barrier identity and phase,
   and an explicit finite CTA/warp participant map. `ThreadLocation.thread` is an
   abstract identity, not currently a proved physical warp/lane decomposition.
2. **Arrival and release transitions.** Fetching an actual barrier instruction
   must record arrival exactly once. Waiting must block further dispatch. A
   complete participant set releases the phase and resumes its waiting threads;
   exits need a separate later extension if excluded initially. Full completion
   should make threads runnable without requiring an unsupported scheduler
   fairness assumption. Runnable does not mean hardware guarantees when they run.
3. **Actual shared-state-space instructions.** `SharedVector` means multiple
   lanes use one allocation, but its underlying instruction forms are global
   loads/stores, not PTX `.shared` instructions. `Environment` already has CTA
   ownership categories; connect them to the new shared access forms. Do not
   relabel a global-memory trace as shared-memory coverage.
4. **Synchronization-bearing traces and graphs.** Current graph effects record
   initialization, loads and stores; ordered scalar event extraction records
   only memory effects. A barrier must survive trace construction with exact
   program origin and phase. Prove that no executed barrier or access disappears
   and that the graph's barrier ordering comes from the collective transitions.
5. **A memory-model connection.** A shared-list interleaving interpreter can
   furnish a constructive execution, but its immediate visibility is not by
   itself a complete PTX semantics. Add the barrier-derived ordering to a
   reviewed relational model or prove the needed specialization. Establish the
   universal result for all candidates covered by that claim, plus a distinct
   completed execution witness. An inert annotation or a premise saying that
   all scratch values are already visible would omit the central obligation.

A simple first program should have no early exits, no data-dependent barrier
choice, and no writes to scratch after the publishing barrier until all intended
reads are finished. Prove its participation and source restrictions from its
instructions, not from a hypothesized successful result. A two-generation test is
valuable even if the first reduction uses only one barrier: it tests that the
resource can actually be reused.

## Distinguishing checks before claiming the milestone

- **Positive cross-warp example:** arbitrary 32-bit input values, distinct aligned
  scratch slots, all participants arrive, and the designated output register is
  their wrapping sum. Include zeros, maximum words and a sum that wraps.
- **Blocked prefix:** schedule one warp through arrival while withholding the
  other. The first cannot execute its post-barrier read. Repeatedly scheduling
  a waiting thread cannot fill the missing arrivals or alter memory.
- **Complete witness:** schedule every participant to arrival, release the
  barrier, then finish the reduction and exits. Prove finite execution, correct
  result and memory safety separately. Do not claim fairness of every schedule.
- **Barrier relevance:** remove synchronization and construct a permitted run
  where a reader sees an old scratch value. Alternatively, for the initial
  operational layer, first demonstrate such an interleaving there and keep that
  narrower evidence distinct from a PTX-permitted graph witness.
- **Reuse:** run two rounds with different data. Arrivals from round one must not
  release round two; no thread may pass its second barrier while another has
  not arrived there.
- **Identity separation:** threads in another CTA cannot discharge the pending
  arrivals even for the same numeric resource. If only one CTA is representable,
  state that exclusion rather than pretending to test general CTA isolation.
- **Boundary checks:** reject unsupported explicit counts, dynamic IDs and forms;
  reject out-of-range IDs as illegal, rather than silently reducing modulo 16.
  Distinguish unsupported legal forms from undefined aligned divergence.
- **Exit boundary:** the first program proves no exit occurs before its barrier.
  Once exit-aware barriers are added, test release when only exited threads are
  missing, and continued waiting when a still-live participant is missing.

These checks complement universal statements; examples alone are not coverage.

## Points that remain interpretation questions

The selected full-CTA, no-early-exit form has a clear intended synchronization
contract. Several larger-family cases need their own investigation:

- The prose does not provide a complete operational algorithm for translating
  explicit thread counts into warp arrivals in the presence of partial warps,
  early exits and repeated `.arrive`. Do not invent that algorithm from the
  simple full-CTA model.
- `.arrive` explicitly requires a nonzero count, while the section does not
  explicitly equate a supplied zero count for `.sync` with omitted count. That
  distinction is irrelevant to the selected no-count form and remains unassigned.
- The broad `.aligned` wording says all CTA threads execute the same instruction,
  whereas the execution paragraphs and `exit` rule exclude exited threads from
  waiting requirements. Do not settle every divergent/early-exit combination by
  silently treating alignment as “same barrier number”. Avoid those combinations
  in the initial slice and document its uniform participation proof.
- Reuse and “same barrier” require a dynamic phase interpretation, but the manual
  does not prescribe our exact Lean representation. Arrival/completion splitting
  is an engineering choice whose source correspondence needs review.

These are boundaries to investigate, not reasons to replace the selected barrier
with assumed visibility or to classify ordinary waiting as undefined behavior.

[manual]: ../../references/nvidia/ptx-isa-9.4/README.md
[cta]: ../../references/nvidia/ptx-isa-9.4/index.html#cooperative-thread-arrays
[bar]: ../../references/nvidia/ptx-isa-9.4/index.html#parallel-synchronization-and-communication-instructions-bar
[exit]: ../../references/nvidia/ptx-isa-9.4/index.html#control-flow-instructions-exit
[scheduling]: ../../references/nvidia/ptx-isa-9.4/index.html#independent-thread-scheduling
[divergence]: ../../references/nvidia/ptx-isa-9.4/index.html#divergence-of-threads-in-control-constructs
[scope]: ../../references/nvidia/ptx-isa-9.4/index.html#scope-and-applicability
[ld]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-ld
[st]: ../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-st
[synchronization]: ../../references/nvidia/ptx-isa-9.4/index.html#memory-synchronization
[po]: ../../references/nvidia/ptx-isa-9.4/index.html#program-order
[cause]: ../../references/nvidia/ptx-isa-9.4/index.html#causality-order
[causality-axiom]: ../../references/nvidia/ptx-isa-9.4/index.html#causality-axiom
[shared]: ../../references/nvidia/ptx-isa-9.4/index.html#shared-state-space
[spaces]: ../../references/nvidia/ptx-isa-9.4/index.html#memory-consistency-state-spaces
[async-po]: ../../references/nvidia/ptx-isa-9.4/index.html#program-order-async-operations
