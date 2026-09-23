# Shared-memory publication across a barrier

Each thread writes one input word into its own slot of CTA-owned shared memory.
All threads then meet at the same unconditional block barrier. After completion,
each reads a selected partner's slot. The partner can be in a different warp;
the example must not depend on threads in one warp advancing together. A concrete
instance uses 64 threads in two warps of 32 and exchanges values between them.

The supplied allocation starts with arbitrary old words. Inputs come from actual
register values, and reads initially have arbitrary candidate values. For each
slot the memory graph contains its initialization, its single program write,
and the appropriate reads by any partners. The graph chooses the source of every
read and an order of writes to a common word. No premise sets a candidate read
to its desired answer.

The full-participation barrier orders every participating pre-barrier store
before every participating post-barrier load. The graph derives these edges
through the completed phase, retaining CTA, resource, instruction-site and
generation identity in the execution connection. Only after forming these paths
does it restrict causality to matching addresses. Source compatibility and the
rule excluding obsolete writes then force each read to select its partner's
program write rather than the initial word. Value agreement follows from that
source identity.

All accesses use explicit `st.relaxed.cta.shared.u32` or
`ld.relaxed.cta.shared.u32`, the generic memory-access mechanism, one shared
allocation and one CTA. No outside thread accesses this allocation during the
fragment; CTA ownership alone would not exclude PTX cluster access by another
CTA. Addresses are aligned four-byte offsets held in 32-bit
address registers and must remain in range without wrapping. These conditions
justify a whole-word representation with mutually included thread scopes.
Reusing the algebra of the earlier graph is an explicit specialization to this
uniform shared window, not general mixed-state-space or alias semantics.

A fresh-source graph witnesses consistent memory choices. Removing cross-thread
barrier ordering also admits a graph reading old values when every reader's
partner is a different thread. This distinguishes ordering from simply placing
stores and loads in a program. A graph witness is separate from instruction
execution: the complete example must connect its labels to fetched instructions,
prove arrival and blocking behavior, construct a finite completed run, and
establish valid accesses to the supplied allocation.

There are no competing program writes to a slot, early exits, conditional
barriers, asynchronous operations or pointer aliases. Fixed addresses and input
register stores make the values independently grounded. The example provides
neither general no-thin-air semantics for dependent programs nor fairness or
hardware-conformance guarantees. PTX 9.4 and targets at least `sm_70` provide the
selected modern memory rules; the barrier itself is available on older targets.

For every finite candidate schedule in which all threads exit, each thread has
exactly one store and one load, and its result register contains its selected
observation. The actual trace contains no other memory effects. If the associated
source choices and write order satisfy the memory constraints including the
completed barrier edges, every result equals the partner's input. This is
correctness on completion; it does not promise that every schedule completes.

A separate constructive schedule dispatches every store, then every barrier
arrival, then every load and exit. It takes four dispatches per participant.
Its concrete execution uses the arena's current values, its graph selects fresh
sources and satisfies every represented memory rule, and its memory projection
is exactly the graph's program events. Initial graph writes match the supplied
old arena. Every access in any finite trace passes the same initial allocation's
checker; allocation identity and ownership stay fixed throughout execution.

The graph's scope information is also checked: all represented threads belong
to the configured CTA, and each program access has CTA scope. Therefore every
pair of program accesses includes the other in its scope. The scope-aware
observation rule agrees with the whole-word rule used here. This scope result
supports the memory interpretation; it does not replace the barrier ordering.
