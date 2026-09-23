# How extra ordering changes a read

Consider three events at one word: its initial value is zero, a thread writes
one, and another thread reads it. A candidate supplies the read value and its
source write. The memory checker asks whether that choice fits all applicable
ordering rules.

Without communication between the threads, the reader can still see the initial
zero in the restricted model. The write and read being listed next to one
another in a file does not order them. If a completed synchronization operation
orders the write before the read, the initial write becomes obsolete for that
read. We must derive this ordering from the synchronization, rather than putting
the expected value into the candidate's premises.

`Ptx/OrderedMemoryExamples.lean` checks precisely this distinction. Both source
choices satisfy the original graph rules. Adding the write-to-read edge rejects
zero and admits one. The latter proof matters: an inconsistent extension could
otherwise "prove" every result by admitting no executions.

## The reusable constraint layer

`Ptx/OrderedMemory.lean` leaves the existing graph unchanged. Its additional
relation describes extra **base-order edges**, before the same-address filtering
used to define causality. Paths may cross addresses; only their endpoints must
match when that part of causality is formed. An observation followed by such a
path is the other allowed construction. Arbitrary chains of causality are not
introduced.

The eight validity fields have the same roles as in the original model. The
`valid_original` theorem proves that no old constraint has been lost.
`empty_valid_iff` recovers the original model when there are no extra edges.
`valid_restrict` checks the direction: more ordering can remove candidates;
it cannot admit a candidate that a smaller set of edges forbids.
`derived_valid_iff` says that adding edges already following from original base
paths has no effect.

The `source_of_latest` proof first uses source compatibility to find a write to
the correct address. If it were a different, earlier write, `no_stale` would
reject it. Only `value_of_latest` then turns source identity into a statement
about the numerical value. These are general proof rules, not assumptions that
a barrier or kernel has worked.

## Where a barrier connection must enter

The separate collective-order certificate splits a phase into arrival,
completion, and resumption. A projected edge follows four structural edges:
memory access → arrival → completion → resumption → memory access. Natural-number
positions prove these paths cannot form cycles. This is why simply connecting
single barrier nodes in both directions would be the wrong representation.

The certificate and extra-order relation are mathematical interfaces. They do
not by themselves prove that actual threads executed a barrier. A complete
application must connect them to fetched instructions, actual arrivals, the
participant set, and the correct CTA/resource/generation. It must connect memory
events to those same instruction executions and justify state-space access and
scope. A separately constructed run must satisfy the resulting constraints.

In particular, the three-event example is an algebraic distinguishing check. It
does not provide shared-memory instruction coverage, hardware conformance, a
general dependent-program memory semantics, or a complete barrier kernel.
