# Independent trace-to-memory review

No blocking issue remains in the reviewed structural projection, ordered
scalar adapter and projected publication example. Reviewed SHA-256 hashes:

- `Ptx/TraceMemory.lean`: `6c5e98e50c93844a6abe70c716767e17a32ad49e6f1578fba67f03ef5f59a512`.
- `Ptx/ScalarTraceMemory.lean`: `35bccf147ba3ec4ea6cdaa0b49a420e91c100769907444e710f71bd86be9e504`.
- `Ptx/ProjectedPublication.lean`: `0daa55f58422ac762e48fc850af90b8873493a9b9f38bc9957bb977b2bed8d39`.

## Structural projection

The trace is numbered before filtering memory effects. Dynamic occurrence
positions therefore include non-memory steps and do not confuse repeated visits
to one instruction PC. `project_member_iff` characterizes both origin and access
exactly at the retained index. `project_complete`, `project_unique` and strict
`project_ordered`/`project_nodup` establish no missing or duplicate projected
occurrence within one trace, relative to the supplied projector. They do not
prove that an arbitrary projector describes instruction execution.

Locations pair a finite catalogue slot with an unbounded word offset. The
injective code `k*word+slot` distinguishes both components; the zero-catalogue
case is vacuous because it has no locations. The catalogue's injective keys
cannot justify physical alias resolution or access permissions by themselves.
Shared keys now include device, grid, cluster, CTA and allocation, preventing
accidental identification of equal local CTA numbers in different grids or
clusters. This corrected an ambiguity found in the preliminary review. Event
assembly now supplies the issuing thread to the projector, so shared location
resolution need not discard that context.

`events` keeps initial writes and all thread projections in one list.
`po_iff` depends on same thread and increasing dynamic position, without splitting
global/shared accesses into unrelated graphs. `same_address_iff` preserves exact
slot/word equality. The graph constructor retains every supplied label regardless
of source/coherence choices. Initialization has no issuing thread; its encoded
location is also used as its position for label compatibility, not as program
execution order.

The generic event constructor does not itself require unique participating
thread IDs or unique initial locations. Its new `events_unique` theorem proves
whole-assembly identity uniqueness when both conditions hold. Initial identities
use their injectively encoded locations with thread `none`; dynamic identities
use `some thread` and occurrence position. Thus cross-thread, initialization
and dynamic-event identities cannot collide. Per-thread order excludes repeated
dynamic positions. A concrete assembly must discharge the two uniqueness
premises, rather than relying on per-thread projection uniqueness alone.
Similarly the generic constructor does not establish that catalogue entries
are live, access ranges are valid, scopes mutually include participants or
values are grounded.
It emits at most one load/store access per occurrence. This is not support for
arbitrary multi-effect, asynchronous or indivisible read-modify-write operations.

## Actual ordered scalar adapter

`access` checks instruction fetch at the occurrence's PC, identity with the
actual erased ordered instruction, executed status, emitted memory effect and
matching load/store kind. It retains the original instruction's memory ordering,
actual value and aligned-word index. `label_recover`, `projection_recover` and
`run_projection` give exact equality with the existing checked ordered scalar
labels, rather than merely equal final output values.

`access_origin` exposes those structural checks. On a forged arbitrary occurrence
it is not an execution proof; its actual-run interpretation comes from the
runner. `access_complete` proves no actual successful memory step is omitted.
`run_access_complete` follows every finite runner case, including later faults,
unsupported outcomes or fuel exhaustion, and excludes memory effects from exit.
`run_project_complete` then retains each actual access at its original dynamic
index. These results neither turn exhaustion into termination nor assume a
complete successful run to obtain trace coverage.

The concrete adapter is the existing singleton global arena, not an actual
mixed-global/shared instruction adapter. A future mixed-space adapter still must
supply storage mapping, access safety, scope and synchronization origin proofs.
No new `Graph.Valid` sufficiency or no-thin-air theorem is asserted. The
trace-memory description makes those semantic boundaries explicit.

## Concrete projected publication

`ProjectedPublication.events` assembles initialization and the two actual
producer/consumer traces through the common projection. It does not take a
separate expected event table as input. `events_recover` and `graph_recover`
prove exact equality with the existing computed publication events/graph for
arbitrary candidate read values, source function and coherence relation. The
old table is used only to prove the list length needed for safe indexing.
Initialization labels and dynamic positions are both recovered exactly.

The concrete `events_unique` discharges the new whole-assembly uniqueness
premises for the four distinct initial locations and threads 0 and 1.
`publication` retains arbitrary candidate read/source/coherence choices, graph
validity and the flag observed in the actual consumer state; it derives the
payload result rather than assuming it. `successful_witness` supplies a valid
graph, halted producer/consumer runs and the previously established acyclic
value-origin relation. `relaxed_witness` keeps the stale-value inequality and
constructs a valid halted consumer with the wrong payload and its own grounded
value-origin witness. Equal old/new values are correctly excluded from the
claim of a wrong result. `memory_safe` covers every event in the four-word graph.

These are transfers of existing restricted publication guarantees through exact
label equality. They do not add general dependent-memory or mixed-space
sufficiency claims. The concrete adapter remains a singleton global arena.

## Independent checks

All three final source files freshly elaborated without warnings or errors.
The targeted `lake --no-cache build Ptx.ProjectedPublication` succeeded with
18 jobs. A fresh import driver printed all 54 explicit public declarations
(36 structural, eight scalar adapter, ten projected publication). The existing
exact-name audit accepted every report with only `propext`, `Classical.choice`
and `Quot.sound`. All source token scans passed and hashes were unchanged after
execution. Complete output is in [trace-memory-audit.txt](trace-memory-audit.txt).
An earlier audit attempt needed the missing scalar adapter object file; after
its targeted build the audit passed. This setup prerequisite was not a proof
failure.

Graph-transport code has its own implementation and verification artifacts;
this review covers the three modules named above.
