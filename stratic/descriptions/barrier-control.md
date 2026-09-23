# Barrier control protocol

This protocol records one full-participation barrier in one CTA, a launched
thread block. Its fixed, nonempty participant set contains every represented
thread; none exits before completion. Each participant arrives at one common
instruction site, identified by a number supplied by the caller. The protocol
is a foundation for executing a barrier, not yet a fetched PTX instruction:
a later execution layer must prove that each request comes from the actual
unconditionally reached barrier at that site.

A barrier key identifies its CTA, its resource number from zero through fifteen,
its instruction site, and its generation, which counts completed uses. A request
with the wrong key leaves the state unchanged and is reported as rejected by the
protocol. This includes old-generation requests and requests from another CTA
using the same resource number. Such a protocol rejection is not a claim about
PTX undefined behavior or hardware fault reporting. The intended first fetched
instruction remains `bar.sync 0` with no explicit participant count.

Each participant has an arrival bit. A clear bit means it may run; a set bit means
it is waiting and cannot dispatch past this barrier. Arrival records that bit
once. Repeated requests from a waiting participant leave all state unchanged and
emit no additional arrival. A fresh request emits an arrival event with its exact
key and participant. When that request completes the whole participant set, the
same transition emits a distinct completion event, clears every bit, and advances
the generation. All participants then become runnable. No fairness assumption
says when a runnable participant will actually be scheduled.

Every state reachable from initialization satisfies the invariant that the
current generation is incomplete: a complete set is immediately released and
reset by the transition that fills its final missing bit. Arrivals can only grow
while the generation stays the same. Any missing participant prevents completion;
arrivals from an earlier generation cannot fill that gap. A finite sequence
containing each participant once completes a generation and can be repeated for
a second generation. These are existence witnesses, not termination guarantees
for every schedule.

An explicit map assigns each thread to a warp, the smaller execution group inside
a CTA. Every reported warp must have an assigned thread. A warp has arrived when
all its assigned threads have arrived. Under the fixed full-participation,
no-exit restriction, all threads arriving is equivalent to all such warps
arriving. This proves equivalence of the completion conditions. Connecting the
individual arrival bookkeeping to PTX warp arrival remains part of the later
instruction-level connection. It does not derive a physical GPU's warp assignment
or assume a universal warp size.

Arrival and completion events have different roles and retain the same generation
key. Their membership and key properties are proved from the transition that
emits them. No memory value, visibility relation, shared-memory instruction,
barrier parser, dynamic resource selection, early-exit behavior or divergent
participation semantics is implemented here. The later memory account must use
these control events and prove its own connection to actual memory accesses.
