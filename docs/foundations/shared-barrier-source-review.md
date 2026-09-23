# Source review: one shared window and a completed CTA barrier

The graph algebra in `Ptx/SharedBarrierMemory.lean` can be reused for this narrow
shared-memory example. That conclusion depends on an explicit connection from
actual shared instructions and a completed barrier to the graph. The earlier
`Graph` module's original global/GPU-scope interpretation is not itself evidence
of shared-state-space coverage. This review supplies the source argument for a
separate specialization; it is not a formal proof that every NVIDIA execution
maps to a graph.

The reviewed source is the pinned PTX 9.4 HTML at
`references/nvidia/ptx-isa-9.4/index.html`, SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The reviewed graph has one initialization and one program store for each slot,
one later load per participating thread, an arbitrary partner selection, arbitrary
initial words, arbitrary input words, and initially arbitrary candidate reads.
Read-source choices and coherence remain variables constrained by validity.

## Why the state-space specialization is justified

PTX §8.3 (`memory-consistency-state-spaces`) states that the memory relations are
independent of state spaces. Accessibility adds a separate restriction: an
operation can directly observe a side effect only if it can access that state
space. This supports reusing relation definitions when their omitted scope,
proxy and overlap conditions are independently discharged. It does not allow
reinterpreting an actual `.global` instruction as `.shared`.

For this specialization all program accesses have the exact forms
`st.relaxed.cta.shared.u32` and `ld.relaxed.cta.shared.u32`. The instruction clauses
`data-movement-and-conversion-instructions-st` and
`data-movement-and-conversion-instructions-ld` allow the relaxed qualifier in
shared space. Their scope/relaxed forms were introduced in PTX 6.0 and require
`sm_70` or later. The source memory model itself applies to `sm_70` or later
(§8.1, `scope-and-applicability`). The project's PTX 9.4 / `sm_70` restriction
therefore suffices for these selected forms; this is not merely a requirement
inherited from the much older `bar.sync` instruction.

The plain `.shared` state-space spelling defaults to the executing CTA's
`::cta` window (§5.1.7, `shared-state-space`). In PTX 9.4, CTA ownership is **not an
exclusive-access guarantee**: other CTAs within a cluster can access a CTA's
shared memory using the relevant forms. The example must expressly exclude
outside-CTA interfering accesses as well as competing writes inside the CTA.
The statement that there are no competing program writes provides this
closed-world restriction; ownership alone would not provide it.

The wrapper must prove that its represented participants are all in the same
CTA and that each accessed address lies in the supplied live shared allocation.
For byte address `base + 4 * slot`, it must establish four-byte alignment, bounds,
non-wrapping arithmetic and that distinct slots do not alias. The graph's natural
slot number is an abstraction of that address, not a byte address in disguise.
All instructions use the ordinary generic *proxy*, meaning the ordinary access
mechanism (§8.6, `proxies`). This is compatible with explicit shared-state-space
addressing; generic proxy and generic addressing are different concepts.

## Strong operations and whole-word reads

A relaxed memory operation is a *strong operation* in the terminology of §8.4
(`operation-types`). Strong does not mean sequentially consistent or release/acquire.
CTA scope contains all threads in the same CTA (§8.5, `scope`); a warp is not a
memory scope. Therefore each pair of represented program accesses to one slot
is mutually scoped, uses the same proxy and overlaps completely. Those are the
conditions for being *morally strong*, the pairwise relation defined in §8.7
(`morally-strong-operations`). Disjoint slots need no moral-strength relation.

PTX's underlying storage units are bytes (§8.2, `memory-operations`). Alignment
alone is not a proof of a uniform whole-word source. The necessary additional
argument here uses §8.10.3 (`atomicity-axiom`): a read and a morally strong write
cannot communicate one byte from that write and another byte from a coherence
predecessor of that write. For each slot the only candidates are initialization
and one full four-byte program write. The initialization is normalized as the
pre-thread initial word, preceding its program write. If a read takes any byte
from that write, single-copy atomicity excludes taking another from initialization;
otherwise all bytes are initial. Consequently every read has a single whole-word
source in this fragment.

The initial word may be arbitrary. PTX §8.2.6 (`initialization`) gives each byte
an initial hypothetical write; absent an explicit initializer its value is
unknown but constant. Grouping those four initial bytes into one word is a
normalization, not a promise of zero-initialized shared storage. This source
argument is separate from `Graph.single_copy`, which merely proves uniformity
of the word model's already-chosen byte-source function.

The argument would need revision for partial overlaps, mixed widths, weak or
out-of-scope contenders, aliases, non-generic proxies, asynchronous accesses or
additional unrepresented writes. It does not settle any broader byte-level
observation policy.

## What the barrier adds

PTX §9.7.15.1 (`parallel-synchronization-and-communication-instructions-bar`)
states that completion makes prior accesses performed relative to participating
threads; `barrier.sync` also prevents new memory requests before completion.
For writes, being performed means the previous value can no longer be read by
those participants. `bar.sync` is the aligned spelling, and the chosen omitted
count means full CTA participation. The model excludes early exits and divergence,
uses one common instruction site and preserves CTA/resource/generation identity.
The separate [barrier source review](barrier-source-review.md) records those
conditions in detail.

The relational account is consistent with that instruction rule. Program order
(§8.9.1, `program-order`) connects an earlier store to its thread's barrier and
the barrier to its later load. Barrier synchronization (§8.9.4,
`memory-synchronization`) connects the relevant participants on the same barrier.
Base causality (§8.9.5, `causality-order`) composes those connections. Splitting
arrival and resumption around completion makes the intended direction explicit
rather than inventing bidirectional edges between unsplit barrier nodes.

For every participating producer and consumer, the desired projected edge is:

```
producer store → producer arrival → same-use completion
               → consumer resumption → consumer load
```

The projection must first form paths across potentially different addresses.
Only then does generic-proxy, same-address preservation restrict the memory
causality endpoints. `Ordered.cause` keeps the existing specified recipe: a
proxy-preserved base path, or observation followed by such a path. It does not
add a further transitive closure to the entire causality relation.

`source_choices` excludes all but the selected slot's initialization and program
store using source compatibility and the exhaustive event table. `source_after_barrier`
then uses the barrier's same-address causality consequence and §8.10.6
(`causality-axiom`) to exclude an obsolete initialization source. Finally
`read_after_barrier` obtains value equality from source identity. Neither the
inputs nor the candidate reads are constrained to a desired answer in advance.
The additional coherence and per-location-cycle constraints come from §§8.9.6,
8.10.1 and 8.10.5 (`coherence-order`, `coherence-axiom`, `sc-per-loc-axiom`).

## Coarse phase levels are proof ranks

The levels store=1, arrival=2, completion=3, resumption=4 and load=5 are a
ranking of structural dependencies. Equal-level operations are not totally
ordered. They do not assert that a hardware scheduler executes every store
before any arrival: one thread may arrive while a peer has yet to store.
`Before` compares an access only with its *own* participant's arrival; `After`
compares it only with its own resumption. Together with same-phase completion,
these produce exactly store-to-load edges. Initialization has no participating
thread and is not accidentally included in the barrier edges.

This is a sound acyclicity technique for the fixed one-store/one-barrier/one-load
shape. A common rank increasing along every relevant edge excludes a cycle;
separate acyclicity of several unrelated relations would not. It would be wrong
to reinterpret rank comparison itself as a universal synchronization relation,
a total issue order, a clock, or a proof that the phase completed.

`phaseOrder` currently uses `Unit` as the phase type, sufficient for a graph with
one selected completed use. That erases identity inside the graph and therefore
makes the wrapper obligation important: it must identify one actual completed
`Barrier.Key`, with the right CTA, resource, generation and site. The same `Unit`
certificate cannot be reused to connect unrelated barrier uses merely because
their resource numbers coincide.

## Remaining connection and review obligations

The relation-level definitions and positive theorem do not yet establish actual
instruction origin. The fetched wrapper must supply the following evidence:

- Exact shared opcode/qualifier origin for every graph event, including its
  issuing thread, incoming store value, selected address and candidate load value.
- Complete event coverage: no relevant load, store or competing external access
  is silently omitted from the modelled execution.
- Arrival follows each store; blocked participants issue no post-barrier load;
  the exact common phase completes; each load follows release.
- The actual input registers and fixed address calculations ground every store
  independently of the candidate reads. Ownership, lifetime, alignment, bounds
  and no-wrap obligations hold for the actual shared allocation.
- A finite instruction execution and valid fresh-source graph witness. These
  establish distinct nonvacuity facts. Neither is a scheduler fairness proof.

Removing barrier edges can admit old-value reads when each reader chooses another
thread's slot. That negative graph is about absence of synchronization. It must
not be presented as a possible stale result for the completed-barrier program.
Self-partners must be excluded from that stale witness because their own program
order already orders the slot's store before its load.

No change to the reviewed graph theorem statements is required by this source
review. Descriptions should retain three qualifications when the wrapper lands:
cluster access is explicitly excluded, whole-word sources require the
single-copy argument rather than alignment alone, and coarse levels express
proof order rather than actual global timestamps. Until the wrapper and witnesses
are complete, the description's complete shared example remains only partially
implemented. Hardware conformance and full PTX shared-memory coverage remain
outside the claim even after this restricted connection is proved.
