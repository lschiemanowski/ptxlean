# Ordering across a completed barrier

When a thread reaches a barrier, its earlier memory instructions have already
been issued. The thread can issue later instructions only after that use of the
barrier completes. For two participants in the same completed use, this supplies
an ordering path from the first thread's earlier access to the second thread's
later access.

The path has four steps: the earlier access precedes its thread's arrival;
that arrival precedes collective completion; completion precedes the other
thread's resumption; and resumption precedes the later access. Arrival and
resumption are separate positions even when an implementation records completion
and release together. They may be placed between machine steps. Treating both
sides as one mutually ordered barrier node would invent a cycle.

A position certificate records the owner of each memory event, the participants
in each completed use, and natural-number positions for memory events, arrivals,
completion and resumption. Each participant's arrival must precede completion,
and completion must precede its resumption. Earlier and later accesses are
selected by ownership and position. No field mentions memory values, read
sources, or a desired result. The resulting cross-barrier edge expands into the
four-step path, and every edge strictly increases position. Both the expanded
paths and the projected memory paths are acyclic. Other memory-order edges may
be included when they too strictly increase these same positions.

This is an ordering projection, meaning a way to remove intermediate control
nodes while preserving their paths. It is not yet a proof that a fetched PTX
barrier produced the certificate. An instruction-level connection must establish
that positions come from an actual control execution, that no relevant access is
omitted, and that the completed-use identity includes the CTA, barrier resource,
generation and instruction site. Participation must be justified under the
full-CTA, aligned, no-early-exit restriction. Those requirements cannot be replaced
by choosing convenient positions after assuming the desired memory result.

The projection does not choose read values or itself justify PTX memory validity.
Its edges order accesses even when their addresses differ; the memory rules apply
address restrictions at the appropriate later stage. Applying it to ordinary
shared-memory operations additionally requires actual shared instruction labels,
one CTA's accessible storage, matching access sizes, and the required scope and
proxy conditions. It does not reinterpret existing global-memory labels as shared
ones. Asynchronous operations and other barrier forms need their own connection.
