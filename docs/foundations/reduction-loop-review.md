# Independent review of reduction control and history

No semantic or proof-contract blocker was found in the reviewed modules. This
review was performed independently of their implementation and covers the final
loop/terminal control and publication/barrier history used by the reduction's
memory and arithmetic results. It does not replace the separate review of the
memory model or claim full PTX scheduling semantics.

Reviewed source SHA256 values:

- `Ptx/SharedReductionLoop.lean`:
  `bce70634731200c8cb37b7e78e21910b158073f7284098d0e96d47a7036e993f`.
- `Ptx/SharedReductionHistory.lean`:
  `29d608d01f34b119cef60b71da24c367bcaf6b29f6651262f08dd999e2c4734e`.

The loop invariant is derived from the fetched program and arbitrary supplied
register/predicate banks. It does not assume the counter or cursor has already
been initialized. The lane-number comparison establishes that only lane zero
can enter initialization, loop and output blocks. The `4*n < 2^32` configuration
bound makes the initialized count exact and prevents lane-number truncation.
Counter subtraction has a strictly positive reachable count, so it cannot wrap
below zero. The pointer invariant explicitly represents the intermediate PC5
boundary after address increment but before counter decrement. Every emitted
shared load is therefore the leader's load at a slot strictly below `n`, even
when the allocation contains additional scratch words. This is stronger than
merely checking that an address fits its allocation.

The terminal invariant separately tracks the actual fetched exits. A follower
can exit only from choose PC2 and has a nonzero lane number. A halted lane-zero
thread must be at output PC1. In this program the preceding store is the only
transition from output PC0 to PC1; a fault leaves the thread before that point.
`halted_leader` thus supplies a useful completion fact without assuming an output
event, successful store, correct accumulator or final memory equation. On a
barrier release, the terminal proof uses the existing waiting-site invariant
to show every released thread was live; it does not revive a halted thread by
forgetting its terminal state.

The history module counts actual emitted shared stores, arrivals and completions.
Publication and phase credits are linked to those counts by one-step balance
proofs, then by induction over the actual dispatch schedule. Initialization
discharges all starting credits. Repeated scheduling of a waiting or halted
thread produces no invented progress. Completion implies every participant has
already published, and publication is at most once per thread. The phase key is
derived from actual fetched barrier requests and the reachable generation zero;
it is not a caller-supplied common-key assumption.

The final-arriving participant receives explicit treatment: the completing step
emits its arrival immediately before the completion event. Other participants'
arrivals lie in an earlier trace prefix. These facts yield each writer's strict
store–arrival–completion–load order. The indexed endpoint
`load_prefix_at_index` locates the specified dynamic load occurrence, preserving
its exact position even when event values or program counters repeat. Its
prefix-length bound places every witness strictly before that occurrence.
The read oracle is shifted by dispatch count, including waiting dispatches,
which agrees with `runWith`; it is not incorrectly indexed by memory-event count.

The history conclusions assume neither fresh read values nor a correct sum.
Actual opcode/event origin is checked separately from the publication filter;
`isPublication_iff` exposes a genuine shared-store memory effect with its data
fields intact. These modules consequently provide execution facts to the memory
adapter rather than replacing visibility with an assumption. The selected
full-CTA, one-resource, one-phase, no-pre-barrier-exit source restrictions remain
necessary. Valid physical launch geometry, target qualification, warp-scheduler
refinement, eventual scheduling and hardware conformance are not established by
these finite control/history theorems.

The guide's phrase “exit at PC7” was clarified during review: that position is
the loop-exit branch transferring to the output block, not the kernel's exit.
No Lean statement or implementation change was needed for this clarification.

Validation performed from the repository root:

- `lake env lean Ptx/SharedReductionLoop.lean` — exit 0; output retained at
  `/tmp/reduction-loop-independent.log`.
- `lake env lean Ptx/SharedReductionHistory.lean` — exit 0; output retained at
  `/tmp/reduction-history-independent.log`. Existing unused-simplifier-argument
  warnings do not affect the checked theorem statements.
- `lake env lean /tmp/reduction-loop-history-review.lean` — exit 0. All 61 public
  declarations were independently enumerated in
  `/tmp/reduction-loop-history-review-public.json`; the report names match that
  inventory exactly, and only `propext`, `Classical.choice` and `Quot.sound` occur.
  Exact reports are retained at `/tmp/reduction-loop-history-review.log`.
- Both source hashes were rechecked after elaboration and matched the values
  above. This review introduces no source, description or common-configuration
  changes.
