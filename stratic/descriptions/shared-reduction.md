# Shared-memory integer reduction

The example adds a finite set of unsigned 32-bit input words. Addition wraps
modulo 2^32, as the selected integer instruction does. Each thread computes its
input address, loads one global word and publishes it to its own shared slot.
All threads then meet one full-CTA barrier: every thread in the cooperating
thread array must arrive before the leader reads the shared words. The leader
uses an actual load-and-add loop with a changing address and repeated program
counters, then stores the sum in global memory.

The whole-program runner fetches the producer, shared-store, barrier, leader
selection, initialization, loop and final-store instructions. Block-qualified
labels identify ordinary branch destinations. Cross-block branches are actual
instructions; they do not rebind registers. The leader sets its counter,
accumulator and pointer with actual moves. A finite schedule proves that all
threads exit, the global output word contains the modular sum, and scratch
contains the published input prefix with its extra words unchanged. Initial
scratch and output words and all otherwise unused registers remain arbitrary.
The exact memory projection of this run contains every producer load/store,
every ordered leader load, and its final global store. This constructive result
is separate from correctness for arbitrary memory-admitted candidate schedules.

The trace-to-memory connection retains the actual dynamic occurrence index,
fetched instruction, computed byte address and value for each access. A program
counter can repeat in the loop, so it cannot identify an occurrence. Global and
shared words with the same numeric offset have different storage identities.
Candidate reads start with arbitrary values; memory constraints require a
matching source write and restrict how accesses may be ordered. Actual stores,
barrier arrivals and completion force every admitted shared read to see its
producer's value, which comes from the initialized global input. Freshness is
proved from these constraints and execution history, rather than assumed.

The supported participants are all threads of one CTA. There is one barrier
resource, one instruction site and one phase, no exits before the barrier, and
no asynchronous or outside interference. Storage consists of initialized,
aligned whole words with no pointer wrap. The global input and output regions
are disjoint, and each thread owns one shared output slot. The fragment uses
explicit relaxed GPU-scope global accesses, relaxed CTA-scope shared accesses,
ordinary generic proxy, and PTX ISA 9.4 with an sm_70-or-later feature condition.
Participant count is positive and fits the explicit counters and storage;
correspondence to a real launch also needs valid target geometry and all actual
CTA threads represented. Finite execution witnesses do not assert scheduler
fairness, hardware conformance or complete PTX dependency semantics.

Every emitted memory access is aligned to a four-byte word and lies within the
selected global or shared allocation. This safety statement holds for arbitrary
candidate read values and thread schedules: invalid accesses produce a fault
instead of a memory event. Each step preserves both allocation lengths, so the
bounds refer to the allocations supplied at the start. Access safety alone does
not establish absence of faults or completion; the constructive execution proof
separately establishes successful completion for its stated storage conditions.

For any finite thread schedule and candidate read choices satisfying those
combined memory constraints, every emitted global store writes the modular sum
to the separate output slot. If the leader exits, global memory contains exactly
that result and every other global word is unchanged. The proof follows the
actual counter, pointer, loaded value and accumulator through the loop. It does
not require a particular schedule or assume a successful output store. A separate
finite execution proves that completion is possible and constructs valid read
sources and write ordering. Its values have no circular justification through
execution-order and read-source edges. This witness does not impose that stronger
condition on every candidate covered by the correctness theorem.
