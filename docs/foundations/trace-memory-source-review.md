# Independent design review: actual traces coupled to whole-word memory

Reviewed 2026-09-24. No implementation changes or model calls. The recommendation
is a reusable *candidate execution interface* plus a separately identified
constructive, grounded subclass. It is not a new claim to complete dependent PTX
semantics. First integrate an integer shared-memory reduction; postpone binary32
until the same execution and memory coupling is exercised end to end.

## Source basis

Read the actual pinned `references/nvidia/ptx-isa-9.4/index.html`, SHA256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The following source passages determine the boundary (anchors are exact):

- §8.1 `scope-and-applicability`: these memory constraints apply on sm_70+;
  texture, including ld.global.nc, and surface accesses are excluded.
- §8.2 `memory-operations`, §8.2.6 `initialization`: operations access bytes;
  hypothetical initial writes supply unknown-but-fixed values absent an explicit
  initializer. One initial word per represented physical word groups those bytes;
  it is not an instruction or a promise of zero-filled storage.
- §8.3 `memory-consistency-state-spaces`: memory relations are independent of
  state spaces; causality closes across all spaces. Direct observation additionally
  requires access to that storage. Therefore one must not prove separate global
  and shared graphs and discard cross-space program-order or synchronization paths.
- §§8.4–8.7 `operation-types`, `scope`, `proxies`,
  `morally-strong-operations`: relaxed operations are strong; scope must be mutual,
  ordinary generic proxy is distinct from generic addressing, and overlapping
  operations in this specialization must overlap completely. Aligned u32 accesses
  may refer to exactly the same word or to disjoint words, never partial overlaps.
- §8.9.1 `program-order`: order is the dynamic per-thread instruction order,
  including repeated visits to an instruction. A PC is not an occurrence ID.
  Asynchronous accesses have explicitly different ordering and remain excluded.
- §§8.9.2/8.9.4 `observation-order`, `memory-synchronization`: qualified actual
  operations supply observation and release/acquire synchronization; actual uses
  of CTA barriers supply their own synchronization. A read source is not itself
  a synchronizes-with edge.
- §8.9.5 `causality-order`: compose base causality before restricting to
  proxy-preserved, same-address endpoints. Final causality also has the
  observation-then-proxy-preserved clause; it is not freely transitively closed.
- §8.10.3 `atomicity-axiom`: a read cannot mix bytes from a morally strong write
  with bytes from its coherence predecessor. For a finite, totally coherent set
  of full-word writes, every read/program-write pair mutually scoped and generic,
  this supports a uniform word source: choose the maximal contributing write and
  exclude all earlier contributors. The special all-initial case groups its four
  fixed bytes. This source argument is distinct from the existing definitional
  `Graph.byteSource` uniformity theorem. Do not apply it to weak, partially
  overlapping, out-of-scope, alias-proxy, or unrepresented competing accesses.
- §8.10.4 `no-thin-air-axiom`: instruction dependencies and communication must
  not justify speculative values circularly. The source expressly allows the
  initialized-zero value in the dependent load-buffering cycle and permits
  independent constant stores in load buffering. It also permits semantic
  reasoning to eliminate apparent dependencies. It does not supply a complete
  syntactic dependency algorithm. Consequently RF+dependency acyclicity is a
  conservative sufficient subclass, not an equivalent formalization of this axiom.
- §9.7.15.1 `parallel-synchronization-and-communication-instructions-bar`:
  omitted count means full CTA participation; bar.sync is the aligned spelling.
  All threads must execute the same aligned barrier instruction, with uniform
  conditional execution if conditional. Arrival waits for non-exited warp peers;
  completion waits for other participating warps, restarts waiting threads and
  reinitializes the resource. Completion makes prior memory accesses performed
  relative to participants, and sync blocks later memory requests until completion.
  The first new example should use one fixed resource, one site, one completed
  phase, no pre-barrier exit, and divergence only after that barrier.
- Selected ld/st relaxed or acquire/release global/shared forms require PTX6.0
  and sm_70+. `bar.sync 0` without count predates this, so ISA9.4/sm_70+ suffices
  for these selected forms. No default weak instruction may be silently promoted
  to relaxed. Shared access by other CTAs in a cluster must be expressly excluded;
  CTA ownership is not by itself an isolation guarantee.

## Small reusable interface

Keep the actual local instruction derivations and shared barrier-control derivation
as the source of truth. Do not make an event-table constructor into a second
independent interpreter. A minimal interface can expose:

1. Finite per-thread actual traces, retaining every executed or skipped dynamic
   occurrence, its PC, fetched typed instruction, register/predicate reads and
   writes, and optional memory effect. Identify an occurrence by (thread,
   dynamic trace index). The index includes arithmetic/branch/skipped events;
   do not re-use PC or a static load number as an oracle key in a loop. Candidate
   read choices are indexed by these dynamic occurrences, not by thread alone.
2. A memory projection derived from each actual effect and fetched opcode. It
   retains actual byte address and value, load/store ordering, state space, scope,
   proxy and issuing thread. Prove both sound origin and completeness, including
   cardinality/uniqueness by occurrence identity: no load/store disappears and no
   event is duplicated. Retain skipped/branch events outside the projected list
   for control reasoning. Fault/unsupported instructions cannot emit admitted
   memory effects. Successful finite paths and completed executions stay distinct.
3. A storage map from actual address expressions to one live logical allocation
   and aligned byte offset. Global and CTA-shared storage identities must be
   tagged, even at equal numeric addresses; owner and lifetime come from Environment.
   An injective encoding of (space, owner/allocation identity, word offset) into
   the existing natural graph address is enough for the bounded interface.
   Distinct virtual aliases of one physical location are excluded initially;
   repeated uses of the *same* address must remain supported. Prove address
   preservation before dividing by four, and prove bounds/no-wrap/accessibility
   for actual computed addresses, not merely input address parameters.
4. Initial events once per represented physical word, plus exactly the projected
   program events. Let RF/coherence be candidate choices. They must not alter
   labels, addresses, local control, or values after the run has been fixed.
5. The original Graph algebra, or Ordered.Valid when completed barriers contribute
   extra base edges. Carry one combined graph across global and shared spaces.
   Initially all participants can be in one CTA on one device; use exact global
   GPU-scope and shared CTA-scope forms, so full overlapping accesses are mutually
   in scope. A global-only mode recovers existing publication. Richer topology
   must use ScopedGraph and its actual side conditions rather than global totality.
6. Every extra barrier edge has an actual same-key arrival/completion/resumption
   path, and before/after refer to each endpoint's own participant. Reuse
   CollectiveOrder's split nodes. Rank numbers prove structural order, not wall
   clock issue time. Never permit arbitrary extra edges as an unchecked claim
   that a barrier executed. The initial reusable version need support only one
   full-participation phase; retain complete CTA/resource/generation/site identity.

This can be a small parameterized trace adapter with realization lemmas for the
existing scalar and shared wrappers. It need not be an extensible event framework
or an instruction-coverage refactor. In particular no unchecked callback named
`decodeMemory` should get to omit events: its totality on actual memory effects
is a required proved adapter obligation.

## Dependency and existence discipline

Separate three results explicitly:

(A) Trace fidelity and memory safety: fields arise from an actual execution and
accessible storage, regardless of whether chosen read values pass graph constraints.
(B) Necessary candidate memory constraints: Sources/coherence/base/causality/
SC-per-location filter candidates. Universal correctness can be proved for this
larger set without first solving all dependent no-thin-air behavior. Graph.Valid
alone is still insufficient as an acceptance criterion for general dependent PTX.
(C) Constructive witness with grounded computation: produce actual terminating
runs, compatible RF/coherence, all graph axioms, and a separate finite grounding
argument for the supported subclass. Do not assume its outputs, termination,
source identity, latest-source property, or dependency acyclicity.

For the first reusable implementation, a conservative grounding order containing
all actual dynamic per-thread predecessor edges plus RF is easier to justify
than claiming to infer every semantic dependency. Include initialization and
initial register/address/predicate inputs as roots. Prove local evaluated values,
addresses, guards and next-PC decisions depend only on earlier roots/reads, then
exhibit a rank for the chosen witness. This intentionally rejects some permitted
PTX load-buffering executions; do not use it to narrow the universal candidate
quantifier or advertise it as a complete admissibility test. A finer optional
relation can later track last dynamic writers of operand/predicate registers;
address and control dependencies must be included, including guard-false steps
and the branch history determining whether a store occurs. Current Op.reads and
Op.writes are useful facts, not a complete dependency semantics. A relation
linking matching register names irrespective of intervening writes is likewise
only a conservative bound, not precise dataflow.

The first reduction has a stronger structural argument: global input loads source
initialization, those grounded values feed unique shared stores, completion orders
every shared store before the leader's loads, then sequential additions feed one
output store. Candidate graph constraints derive each read's source; a phase
ranking proves constructive grounding. This avoids arbitrary dependent feedback.

## Recovering current proofs without assumed answers

- ScalarMemoryWitness already extracts values/addresses from actual run traces;
  its fixed input-source enumeration becomes a generic initialization-only-source
  lemma on the projected graph. Preserve trace equality and existence witnesses.
- ComputedPublicationMachine.label_origin, label_complete and label_byte_address
  are a useful adapter template. Its mapIdx occurrence positions already handle
  gaps. ComputedPublication's current fixed-table proof can remain a specialization:
  derive producer inputs from Sources, identify the flag source from its value,
  then use release/acquire causality to exclude stale payload. Do not place the
  sum or flag publication result in adapter fields. Both existing success and
  relaxed stale witnesses should re-embed unchanged.
- SharedBarrier.memoryOccurrence currently uses PC as position. That is sound
  for its fixed store/sync/load/exit sequence but must change in any reusable
  loop adapter. Its observations:Fin n→Word also deliberately supports only one
  load per participant. SharedBarrierHistory's arbitrary-schedule load_path and
  Frame/Control exact counts provide genuine completed-phase origin. Preserve
  these proofs; a general interface should consume them or reprove the same
  contract, not replace them with a phase-rank annotation.
- OrderedMemory is already the right relation-level extension. Its extra argument
  deliberately does not supply execution origin. Reusable adapters add that
  origin while preserving its original final-causality recipe and restriction lemmas.

## Concrete integration target

Recommend a first 32-thread, single-CTA u32 reduction, then a 64-thread instance
if the generic participant proof is inexpensive. Each lane starts with its
explicit lane identity and actual pointer parameters. It computes its byte
address, loads one initialized global input, and stores that value into its own
shared slot. All execute `bar.sync 0` at one common site without early exit.
After completion, lanes other than zero branch to exit; lane zero loops through
all shared slots in increasing index order, adds them modulo 2^32, stores one
word to a separate valid global output slot, and exits. The lane identity is an
explicit execution input until the relevant special-register frontend is linked;
do not pretend the framework has already modeled runtime launch geometry.

This target exercises global and shared accesses, computed addresses and values,
true repeated PCs, predication/branches, one real completed collective phase,
and actual final storage. It uses the already supported u32 add/compare/address
operations, not new floating-point instructions or warp shuffles. Disjoint global
input/output allocation is a stated restriction of this *new example*, not a
retroactive weakening of affine's unrestricted address aliases. Shared scratch
is live until all threads complete, initialized arbitrarily and overwritten once
per slot. Exclude host, peer-CTA and async interference explicitly.

Required results: every completed admitted candidate stores the modular fold sum;
every memory event has exact instruction/address/value origin; every access is
safe; exactly one shared write per slot and all leader reads follow the completed
phase; output, untouched global words and other allocations have exact frames;
construct finite terminating execution and valid RF/coherence for every input;
prove a grounding rank. No-fairness claim follows from the finite schedule witness.
A loop counter with a fixed finite bound is the termination argument, not fuel
exhaustion being called success. A two-warp 64-thread test is valuable for checking
that the barrier's abstract all-thread condition has not become warp-local.

Useful negative checks: omit the barrier and admit a stale non-self shared read;
change memory projection to drop a load and fail completeness; reuse PC indices
in the loop and fail uniqueness/program-order; conflate global/shared offset zero
and fail storage identity; change branch predicate and fail final-state/trace
contract; drop a participant before the aligned barrier and reject the supported
control certificate. These are behavior checks, not changes to source semantics.

## Remaining substantive limits

The PTX prose no-thin-air clause remains underspecified as a general executable
formal rule; a proved finite grounding subclass is the honest scope. Full
single-copy/byte-model equivalence is still a source-reviewed argument unless a
separate byte-level lifting theorem is provided. Warp arrival dynamics, arbitrary
divergent barriers, multiple barrier phases, weak/out-of-scope mixed access,
physical alias mappings, async operations and hardware conformance remain outside
this first interface. Nothing here depends on paid models or requires rewriting
already accepted scalar instruction semantics.

## Concrete module boundary for the coordinator

A suggested first new module is `Ptx/TraceMemory.lean`, importing only the root
scalar/event/environment/memory foundations. It can stay independent of the
future cooperating scalar wrapper. The minimal generic API is approximately:

```
-- Names illustrative; actual event interpreters remain in adapter modules.
structure Access where
  storage : StorageKey       -- global allocation, or fully qualified CTA-shared allocation
  byteOffset : Nat           -- actual finite address's toNat after its checked translation
  kind : LoadOrder ⊕ StoreOrder
  value : Word
  scope : Scope
  proxy : Proxy              -- restrict admissible records to ordinary generic initially

structure TraceView (Thread Event : Type) where
  trace : Thread → List Event
  memory : Event → Option Access
  -- No Graph.Valid, desired result, or barrier-origin hypothesis here.
```

Use a finite injectively numbered thread set and form
`initialEvents ++ join (threads.map (fun t => (trace t).mapIdx ... |>.filterMap id))`.
Every graph program label gets that thread number and the *mapIdx* index, plus a
canonical injective word-location code. Initialization labels have no thread.
Expose graph construction parameterized only by RF/co, with graph.event fixed
by this list. An access retains actual space/storage and byte address even if
the graph algebra consumes its word-location code. The initial domain must be
unique by physical word identity; an aliasing access reuses the same initial word.

Prove generic `project_member_iff` (there is an exact thread, trace position and
Some access), `project_complete` (every Some access at every trace position has
one corresponding program event), `project_unique` (occurrence identity is
injective), order preservation, and address/value/kind preservation. Prove
`graph_program_labels` as an exact equality of the noninitial labels to the
projection. Prove an event-enumeration equivalence/reindexing lemma that transports
Sources/coherence/Valid/Ordered.Valid through an index bijection preserving labels,
RF/co and extra edges. This enables existing fixed publication and barrier
families to instantiate the generic construction and prove *projection equalities*
to their known tables, then transport the existing theorems. It avoids inventing
new hand-enumerated tables for each future instruction program.

A later `ScalarTraceMemory` adapter proves `memory` is complete and faithful to
actual fetched steps, with exact qualifiers obtained from the typed wrapper and
safety from its execution derivation. `CollectiveTraceMemory` adds an actual keyed
completed-phase origin certificate and produces `extra`; it does not alter the
original scalar semantics or put an arbitrary callback into the trusted boundary.
The existing control/history proofs can discharge this adapter first. If the
generic API stores proof fields, only structural fidelity fields belong there;
accepting `∀ read, value=expected` or a desired final-state property is disallowed.

The first `Candidate` package should visibly separate `traceRealized`, safe access,
all-in-scope/whole-word restrictions, and necessary `Ordered.Valid`; a separate
`GroundedWitness` theorem supplies constructive ranks for selected runs. General
read-dependent branches and address calculations are allowed in the projection
because it reads actual trace fields, but constructing a grounded witness for
an arbitrary such program is not promised. This is useful generality without a
claim to solve the missing general dependency semantics.

For participant-count generality: with an **omitted** barrier count, the source
says all threads of the CTA participate; the explicit-count multiple-of-warp-size
restriction does not itself require a full-CTA size divisible by32. Therefore a
positive `n` can parameterize the mathematical participant model provided all
actual CTA threads are represented and target launch limits and actual warp
membership are explicit environment obligations. Retain the existing abstract
warp completion-predicate limitation; do not infer a complete warp scheduler.
Use n=32 and n=64 as concrete source-eligible integration instances. If abstract
positive-n proofs cost little, prefer them; do not expand to partial-participant
barrier counts, exits before completion or multiple phases to obtain that parameter.
