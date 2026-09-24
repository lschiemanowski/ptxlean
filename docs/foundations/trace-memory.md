# From instructions to a memory graph

The instruction machine answers what each thread does after receiving proposed
read values. The memory graph answers which proposed observations satisfy its
represented ordering constraints. Their connection must retain the actual
instruction values and addresses; a separate plausible event table is not enough.

`Ptx/TraceMemory.lean` supplies the common structural projection.
`Ptx/ScalarTraceMemory.lean` proves a concrete adapter for the ordered global
scalar machine. `Ptx/ProjectedPublication.lean` builds the earlier publication
example through that adapter. `Ptx/GraphTransport.lean` changes representation
without changing the memory obligations. This division separates a general
list/graph mechanism from the proof that particular labels really describe
executed instructions.

## A repeated instruction is a new occurrence

A loop can visit instruction9, execute instruction4, then revisit instruction9.
If the two visits to9 are loads, their projected positions are0 and2. They are
not both position9. Numbering happens before the nonmemory instruction is
removed. The original trace item remains in each projected record.

`project_member_iff` proves exact origin and completeness: membership is
equivalent to finding that original item at the recorded index and identifying
its access. `project_ordered` proves strictly increasing positions, and
`project_nodup` rules out repeated records. `events_unique` extends uniqueness
to the assembled graph when thread identifiers and initial storage locations
are each listed once. These are structural conditions, not a desired memory
value or a termination assumption.

An arbitrary callback that always returns no access would satisfy the generic
list theorems. It would not satisfy the scalar adapter's `run_project_complete`:
that theorem requires every actual memory effect at its actual trace index to
appear. `access_origin` gives the matching fetched instruction, true guard,
actual effect, address, value and ordering qualifier. The existing scalar access
safety theorem justifies recovering the full byte address from its aligned word
index. A failed, unsupported or exhausted run is never renamed a completed run.

## Different storage, one order

A storage catalogue names distinct live allocations. Locations contain a
catalogue slot and a word offset. With k slots, graph address `k*word+slot`
encodes both; division and remainder recover them. The proof requires no fixed
maximum word count. A catalogue with no slots cannot supply an access location.

A global allocation and CTA-shared allocation are different keys. Shared keys
include device, grid, cluster and CTA identities, so equal local CTA numbers in
different launches cannot alias by accident. The projection may use the issuing
thread to resolve its storage. Numeric pointers alone are not storage identities.
Actual address translation, alignment, bounds, ownership and allocation lifetime
remain the concrete adapter's obligations. This module does not invent physical
alias resolution or permission to access another allocation.

All spaces remain in one graph. For example, program order may connect a global
write to a shared access and then another global access. The intermediate shared
access cannot disappear from the path merely because its address belongs to a
different space. `TraceMemoryExamples` checks that distinction as well as repeated
instruction visits and equal numeric offsets in different allocations.

## Reusing earlier proofs

The ordered scalar adapter uses one global catalogue entry, so its encoded graph
address is exactly the previous word address. `label_recover` and
`projection_recover` establish literal equality with the old labeling function.
The publication graph is assembled from initialization and both actual thread
traces; `graph_recover` proves equality with the previously checked graph.

Consequently the positive publication theorem still quantifies over arbitrary
compatible source and coherence choices. The successful witness still finishes
both threads and has a finite value-grounding argument. The relaxed witness
still permits the old payload, and safety still concerns the actual addresses.
These are recovered proofs, not a new assumption that the projected values equal
the expected answer. The old table appears only as an already proved length fact.

When a different enumeration or address code is useful, graph transport uses a
bijection on event identities and an injective address map. Both ordinary and
barrier-extended validity are preserved and reflected. The same event values,
orders and source choices remain visible after renaming. See the accompanying
`graph-transport.md` for the exact APIs.

## What this does not settle

This is a whole-word, ordinary generic-access interface for strong operations
with mutual scope coverage, not the entire PTX memory model. It does not address
mixed sizes, physical aliases, asynchronous operations or out-of-scope accesses.
An actual instruction run plus `Graph.Valid` is still not a sufficient admission
test for arbitrary programs with read-dependent values, addresses or branches.

PTX9.4's no-thin-air discussion permits some initialized dependency cycles.
Forbidding all cycles would exclude permitted behavior. Concrete examples can
instead prove their selected execution is grounded in initial inputs; that is a
sufficient witness argument, not a complete characterization of every PTX run.
Similarly, an extra graph edge does not prove that a barrier executed. A concrete
control trace must supply its keyed arrivals, completion and resumptions.

The independent source review is retained in `trace-memory-source-review.md`.
The implementation review and exact dependency reports distinguish Lean validity
from this source correspondence and its explicit remaining limits.
