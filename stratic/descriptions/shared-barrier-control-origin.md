# Control origin of shared barrier ordering

The four-instruction shared-memory program must justify its barrier ordering
from actual execution. A thread first stores at program counter zero, waits at
one, loads at two and executes exit at three. Reaching three does not yet mean
exit has executed; a halted thread is always at three.

Before completion, the barrier generation is zero and every thread is at zero
or one. An arrived thread remains at one. A final fresh arrival can release the
group only after every participant is at that same barrier instruction. Release
advances all those participants to two and changes the generation to one. After
that transition, all arrival bits are clear and every thread is at two or three.
No second generation can be reached by this program.

These properties must hold for every finite schedule, including repetitions of
waiting or halted threads and failures of access checks, with arbitrary candidate
read values. They do not require an assumed output value or assume that each
thread has arrived. A run may stop before completion; no fairness or termination
claim follows from preservation of the invariant.

The control account also tracks forward progress of program counters and the
completion event emitted by the actual final-arrival transition. The intended
connection to memory ordering must distinguish these trace facts from convenient
phase ranks. Program counters and event origins supply evidence for stores before
arrival and loads after completion; ranks alone do not supply execution history.

For a run beginning with the initial barrier, reaching generation one means the
trace contains exactly one completion and exactly one arrival from every
participant. Event counters are balanced against the actual generation and
arrival bits at every step. Successful stores and loads are similarly counted
against program-counter changes, so advancing a counter cannot silently replace
a missing memory event.

Each actual arrival has its thread's store in an earlier schedule prefix. Each
actual completion has every participant's store in an earlier prefix. Each load
has a prefix containing the completion and all participants' arrivals. Emitted
barrier events carry precisely the configured CTA, resource zero, generation
zero and instruction site one. An initially live thread is halted exactly when
its exit-at-three event occurs in the trace. These statements hold for arbitrary
finite schedules and proposed load values; they do not certify those memory
values as permitted PTX observations.
