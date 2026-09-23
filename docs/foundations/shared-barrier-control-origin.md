# Why the shared barrier's control ordering is real

`Ptx/SharedBarrierInvariant.lean` proves properties of every finite `runWith`
schedule of the fetched four-instruction program. It does not assume a convenient
schedule, valid read answers or that the barrier has already completed. Failing
an ownership/address check, retrying a parked thread, or scheduling a halted
thread cannot break its control invariant.

The useful starting point is `Control.initial`. Supply only that every thread
starts live at PC zero and the barrier equals `Barrier.initial`. There is no
initial register, address, memory-content or ownership premise for this
control-only theorem. An invalid allocation can prevent progress, but cannot
manufacture a successful store or barrier arrival.

`Control` separates two phases:

| Barrier generation | Reachable control state |
| --- | --- |
| 0 | Every PC is zero or one. Any arrived thread is parked at one. No thread has halted. |
| 1 | Every PC is two or three. Every arrival bit is clear. |

No other generation is reachable, and every PC remains at most three. A halted
thread is at three. The converse needs the exit event: the load advances to PC
three before exit executes. `halted_iff_exit_event` proves that an initially live
thread is halted exactly when its actual `exited thread 3` event occurs.

The critical release proof is `all_at_barrier`. The final arriving thread was
fetched at PC one. Every other participant whose bit was already set must also
be at PC one by the invariant. Thus the fact that marking the final thread fills
the arrival set establishes that *all* participants are at the barrier. The
machine's group advance therefore sends every PC from one to two. This conclusion
is derived, not supplied as an additional release premise.

`step_properties` proves preservation, nondecreasing PCs and an exact equation
between generation change and emitted completion count. `run_properties` lifts
those facts to arbitrary schedules. Per-thread arrival accounting remembers a
completed generation even though release clears the bits. Therefore
`completed_exactly_once` and `all_arrived_exactly_once` show that any run reaching
generation one contains one completion and one arrival for each participant.

Memory-event accounting is separate from memory correctness. Leaving PC zero
requires an actual emitted store; reaching PC three requires an emitted load.
`run_memory_balance` relates these counts to the PCs for arbitrary schedules.
An immediate update or a proposed load result still has to pass through the same
actual fetched instruction and event machinery.

`step_event_control` identifies an event's control origin. Stores occur at PC
zero in generation zero. Loads occur at PC two in generation one. All barrier
keys have the configured CTA, resource zero, generation zero and site one.
Exits occur at PC three in generation one. The machine's existing origin and
completeness theorems connect event membership to actual dispatch; this module
adds the reachable-control consequences.

The prefix theorems expose the ordering needed for a memory graph:

- `arrival_has_store_prefix`: an arrival has that participant's store in a
  strictly earlier schedule segment.
- `completion_has_stores_prefix`: a completion has every participant's store
  in an earlier segment.
- `load_has_completed_prefix`: a load has the completion and all arrivals in an
  earlier segment.

`run_event_prefix` also supplies the exact trace decomposition around the event's
step, so these are facts about the real finite trace. The last arrival and its
completion can share one transition; the machine records the arrival first and
the completion second. No global timestamps or simultaneous warp schedule are
assumed.

These results provide control origin for the structural phase ranks. They do not
select read sources, prove that candidate reads are permitted by PTX, identify
the actual data/address fields of each event, or prove that an arbitrary schedule
terminates. The separate frame layer establishes data/address preservation;
the source-reviewed memory graph rules constrain observations. The program's
canonical schedule supplies finite existence without a fairness claim.

The scope remains one unconditional, full-participation, no-early-exit
`bar.sync 0`, with the explicit shared operations of the fixed program. General
barrier reuse, divergent participation, alternative instruction streams and
asynchronous operations are outside these control proofs.
