# Topology, storage contracts, and scoped memory

The environment has two responsibilities: identify which threads a synchronization
scope includes, and check a supplied storage contract for an access. These are
different questions. A system-scoped operation does not grant access to another
thread's local allocation or to an unrelated CTA's shared allocation.

The implementation is in [Environment.lean](../../Ptx/Environment.lean),
[ScopedMemory.lean](../../Ptx/ScopedMemory.lean), and the checked examples in
[ScopedExamples.lean](../../Ptx/ScopedExamples.lean). The pinned source remains
[PTX ISA 9.4](../../references/nvidia/ptx-isa-9.4/README.md).

## Thread identity and scope

`ThreadLocation` records device, grid, cluster, CTA, and thread identities. Its
CTA identifier is an abstract name qualified by the containing cluster; it is
not an assertion about the raw numerical value of `%ctaid`. Grid identity is
included in both CTA and cluster comparisons. Equal local CTA numbers in
different grids therefore do not imply membership in the same CTA.

`Scope.includes` follows [§8.5](../../references/nvidia/ptx-isa-9.4/index.html#scope):

| Scope | Included device threads |
| --- | --- |
| `.cta` | Same device, grid, cluster, and CTA |
| `.cluster` | Same device, grid, and cluster |
| `.gpu` | Same device, including different grids |
| `.sys` | All represented threads of the host program |

Host execution is not represented. Thus the `.sys` row models membership of
device participants, not a complete host/device execution model or a claim of
system-wide atomicity. NVIDIA separately qualifies host-memory atomicity in
[§8.1.1](../../references/nvidia/ptx-isa-9.4/index.html#limitations-system-scope-atomicity).

`Program.TopologyWellFormed` requires distinct used thread identifiers to map to
distinct full locations. Both scoped message-passing witnesses discharge this
condition. A raw `ScopedGraph`, like the existing raw `Graph`, can still contain
arbitrary labels; its memory predicate alone does not validate a launch.

Mutual inclusion is checked in both directions. A GPU-scoped release paired
with a CTA-scoped acquire in another CTA is not enough. The checked regression
`scope_inclusion_is_mutual` demonstrates this asymmetry. The underlying moral
strength rule also retains the independent same-thread program-order clause
from [§8.7](../../references/nvidia/ptx-isa-9.4/index.html#morally-strong-operations).

## Allocation-relative storage contracts

An `Address` contains a state space, allocation identity, and byte offset. It
is already resolved: generic address-window conversion, virtual aliases,
pointer provenance, allocation creation, and deallocation are not implemented.
An `Allocation` supplies extent, a guaranteed base alignment, ownership, read
and write permissions, and a whole-allocation initialization certificate.

`Environment.checkAccess` checks:

1. The allocation exists and the state space agrees.
2. The owner permits this thread to access the allocation.
3. The width is positive and the complete byte range is inside the extent.
4. The supplied base-alignment guarantee and byte offset imply alignment to the
   access width.
5. The requested access has permission, and a read has known initial contents.

The theorem `Environment.accessible_contract` extracts these consequences from
a successful check; `accessible_bounds` is a smaller bounds/alignment interface.
The alignment test is sufficient under the supplied allocation guarantee; it
does not claim that a failed guarantee proves the actual base address misaligned.

Ownership follows these restricted interpretations of the manual's
[state spaces](../../references/nvidia/ptx-isa-9.4/index.html#state-spaces):

| Space | Represented ownership/access contract |
| --- | --- |
| Global | System-accessible allocation, or an allocation restricted to one device |
| Shared | Owning CTA; an explicit cluster-access view may address a peer CTA |
| Local | Exactly the owning thread |
| Parameter | Read-only entry parameters of the owning grid |

For peer-CTA shared access, being in the same cluster is necessary but not a
lifetime proof. The caller must establish that the peer CTA is active for the
access, as required by [§2.2.2](../../references/nvidia/ptx-isa-9.4/index.html#cluster-of-cooperative-thread-arrays).
`checkAccess` does not model CTA lifetimes. Function parameter storage, call ABI
rules, and parameter stores are explicitly unsupported. Entry-parameter writes
are rejected even if a malformed supplied allocation marks them writable.

An `uninitialized` diagnostic means that this storage contract does not supply
known initial contents. It does **not** mean that PTX has no initial write or
that reading unknown initial contents is universally illegal. The manual's
[initialization rule](../../references/nvidia/ptx-isa-9.4/index.html#initialization)
assigns an unknown constant initial value where no explicit initializer exists.
No code silently fills an unknown allocation with zero. These diagnostics are
contract failures, distinct from instruction-form legality.

## Instruction eligibility

`MemoryForm` describes selected scalar 32-bit explicit-space load/store forms.
`scope = none` denotes omitted ordering qualifiers, whose default is weak; it
does not denote an explicitly written `.weak` modifier. A present scope denotes
the supported relaxed/acquire load or relaxed/release store family; the typed
instruction supplies the ordering direction.

`memoryEligibility` records the version and target requirements from the
[load](../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-ld)
and [store](../../references/nvidia/ptx-isa-9.4/index.html#data-movement-and-conversion-instructions-st)
notes: scoped forms require PTX 6.0 and `sm_70`; cluster scope or explicit
shared-cluster addressing requires PTX 7.8 and `sm_90`. Scoped forms are allowed
only for global/shared space. Plain represented load/store forms start at PTX
1.0. The project targets the pinned PTX 9.4 document, so later ISA versions are
reported unsupported. This classifier covers the listed forms, not arbitrary
PTX syntax, target-feature suffixes, caches, proxies, vectors, or conversions.

Eligibility, storage accessibility, and memory consistency remain separate
predicates. A `supported` result alone establishes neither access safety nor
semantic correctness. Likewise the allocation contract checker is not an
instruction parser or a complete undefined-behavior classifier.

## Scoped relations and partial coherence

`ScopedGraph` adds per-event scopes and a thread topology to the existing
whole-word graph. Read sources and values still come from real `Program`
instruction traces via `Program.scopedGraph`. Initialization remains normalized
to initial writes with no issuing thread. All program accesses in this module
are strong, scalar, whole-word, global, and use the generic proxy.

Moral strength now requires the documented scope condition (or local program
order). Observation, synchronization, base paths, causality, and per-location
constraints are then derived from it. Causality retains the original two
clauses; it is not silently replaced by its transitive closure.

One essential change concerns [§8.9.6 coherence](../../references/nvidia/ptx-isa-9.4/index.html#coherence-order).
The original single-device GPU fragment could order all same-address writes.
The extension instead requires comparability for morally strong writes and
the documented ordering for causally related writes. Its `Coherent.justified`
field prevents adding coherence edges between unrelated racy program writes.
The initialization normalization is handled separately. The checked
`racy_writes_partial_coherence` example has two writes in separate CTAs, neither
ordered before the other; `racy_not_legacy_valid` shows why the old totality rule
would reject this candidate.

There is an exact bridge, rather than an informal compatibility claim:
`ScopedGraph.valid_legacy` proves equality of the new and old validity predicates
when every non-initial pair is mutually in scope. `gpu_specialization` applies
this to every word value, source map, and coherence choice of the actual
message-passing program with all accesses GPU-scoped on one device. The old
definitions are unchanged.

## Publication and the missing scope guarantee

The generalized `ScopedExamples.publication` theorem says that an acquire flag
read observing `1` forces payload `7` whenever the release and acquire endpoints
mutually include one another and the candidate satisfies the scoped constraints.
It does not require every event to have the same scope.

`in_scope_execution_exists` supplies a completed same-CTA execution with CTA
scopes and final registers `(1,7)`. `outside_scope_execution_exists` uses the
same release/acquire instructions, puts the threads in different CTAs, and
supplies an admitted candidate with final registers `(1,0)`.
`outside_scope_no_sync` checks the missing synchronization. These are generated
local executions with explicit bounds and injective topology, not hand-written
event tables standing in for programs.

The outside-scope result has an additional coverage boundary: whole-word read
sources restrict this model to **non-torn candidates**. PTX's single-copy
guarantee for morally strong pairs does not justify imposing that restriction
on all out-of-scope races. The stale candidate remains a useful witness of the
lost publication guarantee; this extension is not a complete classification of
the byte-level results of raced PTX accesses. Mixed-size overlap remains absent.

`Program.ScopedAdmitted` currently combines arena bounds, topology validity,
and the scoped relational predicate. It does not include `Environment.checkAccess`
or `memoryEligibility`: the existing trace language still describes its original
global word arena. Those separate interfaces are available for explicit
integration with scalar execution, and that integration must prove its own
contracts. No claim is made here about arbitrary dependency-bearing scalar
programs satisfying all PTX no-thin-air obligations, all schedules terminating,
compiler lowering, or GPU hardware conformance.

## Checked scalar arena bridge

[`Ptx/ScalarEnvironment.lean`](../../Ptx/ScalarEnvironment.lean) connects the new
scalar machine to the allocation contract. `arena_access_iff` proves equivalence
between its aligned word-index check and the full byte-extent check for an
explicit initialized global allocation. `run_environment_safe` applies this to
every emitted scalar memory effect. `separate_arenas` exposes distinct resolved
allocation identities, and `arena_forms_eligible` checks the chosen relaxed
GPU/global forms at PTX 9.4/sm_90. These bridges establish access contracts, not
an unproved concurrent refinement or physical launch mapping.
