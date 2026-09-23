# Shared-memory publication through a barrier

Every thread stores one input word in its own shared-memory slot, reaches the
same full-CTA barrier, reads a selected partner's slot, and exits. The barrier
is the actual instruction between the store and load. It prevents any thread
from executing that load while peers are still missing. Inputs and the old shared
contents are arbitrary. The selected partner is an explicit map between the
finite participants; a concrete launch can choose partners in another warp.

The typed program is `st.relaxed.cta.shared.u32 [a0], r0; bar.sync 0;
ld.relaxed.cta.shared.u32 r1, [a1]; exit`. A program counter selects the instruction
actually fetched. Shared addresses occupy 32-bit registers: thread i initially
has a0 equal to four times i and a1 equal to four times its partner's index.
The arena contains one initialized word per participant, belongs to the configured
CTA, and satisfies the explicit bound four times the participant count is less
than 2^32. This prevents address wrapping. Accesses check ownership, four-byte
alignment and arena bounds. No outside thread accesses this allocation during the
fragment. CTA ownership alone would not exclude permitted cluster access from
another CTA. This does not certify an external allocator or launch.

A barrier request is derived from the fetched resource, actual instruction site,
CTA and current generation. Waiting blocks further dispatch; rescheduling a
waiting thread emits no duplicate arrival. The final arrival releases the group
and advances all participants past the barrier. Reachable-state proofs establish
that those participants are at the common barrier site and that none exited
before reaching it. This wrapper has one barrier visit; general reuse belongs
to the separate control protocol and is not claimed for this program frontend.

Memory events preserve the actual fetched shared-state-space instruction, thread,
site, 32-bit address, ordering and register-derived value. Barrier arrivals and
completion remain distinct keyed events in the same control trace. Origin and
completeness proofs connect emitted effects to dispatch; an ordinary global load
or store is not relabeled as shared-memory coverage.

Every step preserves the input register r0, all shared-address registers and the
arena owner. These frame properties hold for arbitrary scheduling, including
blocked and unsuccessful dispatches. Consequently a reachable store has the
initialized input and own-slot address, and a reachable load has the initialized
partner-slot address. This connects the data fields to the program independently
of the particular schedule used to construct a completed witness.

After any finite candidate schedule, a thread that has completed its load retains
that load observation in r1. In particular, every halted thread has that result.
This invariant is independent of whether the memory model permits the proposed
observations. Completed threads each have exactly one store and one load in the
actual trace; repeated scheduling cannot create additional accesses.

Candidate execution permits explicit proposed load observations while retaining
all control and access checks. Its final result register contains that actual
observation. Concrete execution instead reads the current shared arena. A finite
schedule that stores every input, arrives every participant, reads every partner
and exits every thread gives a completed concrete witness. Its result, access
safety and control completion are separate guarantees; no fairness of arbitrary
schedules is inferred.

The actual history of every emitted load contains, in order, each producer's
store, that producer's arrival, the common completion and the load itself. This
is proved for arbitrary finite scheduling, with the exact CTA, resource zero,
generation zero and site one retained. It is not inferred from coarse graph
ranks or from the particular schedule chosen for the existence witness.

Immediate updates in the concrete arena are a way to construct a witness, not a
complete PTX memory model. Universal partner-read correctness requires a separate
proof connecting actual barrier ordering and shared-memory source choices. This
wrapper supplies the required instruction effects and control trace rather than
assuming that reads already obtained the right values. Warp placement, a concrete
multi-warp launch, memory-graph correspondence, raw PTX parsing, divergent
participation, early exits, explicit barrier counts, multiple barriers and
asynchronous operations remain separately stated responsibilities.
