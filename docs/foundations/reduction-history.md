# Actual publication history in the reduction

`Ptx/SharedReductionHistory.lean` proves where stores, arrivals and completion
occur in the actual fetched execution trace. Its statements allow every finite
schedule and every candidate-read oracle. They do not assume a desired sum,
fresh shared reads, correct input values, or a chosen order of thread execution.

## Two small progress counters

`publicationCredit` is zero before the thread's publication instruction, and one
after it. `run_publication_balance` proves that its increase is exactly the count
of that thread's actual shared-store events. The count inspects genuine scalar
memory effects, as `isPublication_iff` makes explicit. Since the credit is at
most one, `publication_at_most_once` rules out duplicate publications, even if
threads are repeatedly scheduled or later fault. The separate data layer proves
that this store uses its issuer's slot and the word from its earlier global load.

`phaseCredit` is zero in producer, publication and barrier blocks, and one in the
continuation blocks. `run_phase_balance` proves that each thread's credit increases
by exactly the number of actual completion events. `phase_progress` and
`publication_progress` state the corresponding monotonicity. These are coarse
progress measures; they do not prohibit backward branches inside the leader loop.

Completion counting also agrees with the protocol generation, and arrival
counting agrees with generation plus the thread's waiting bit. From the actual
initial state these facts prove at most one completion, and identify every
barrier event with the exact key `(CTA, resource 0, generation 0, site 5)`.
The site number is the machine's identifier for its unique fetched barrier label,
not an instruction position in the dynamically growing trace.

## Constructing an ordered path

`arrival_has_store_prefix` finds a strict earlier schedule prefix containing
exactly one publication by the arriving thread. `arrival_path` converts that
count into an actual store/arrival sublist of the trace. A sublist preserves
order while allowing unrelated events between its members.

The completing dispatch emits its own arrival immediately before completion.
Every other participant's arrival is already in the preceding trace, because
its actual waiting bit is set and its arrival count is one. `completion_path`
therefore constructs, for every writer, the ordered sublist

```
writer's shared store → writer's arrival → common completion
```

This path also holds for the final arriver; its arrival and completion are two
ordered events from the same dispatch. `completion_has_stores_prefix` separately
shows that all participant stores occurred in earlier dispatches.

The leader's shared load can only come from the fetched loop block. Its phase
credit proves that a completion is present in the strict earlier schedule
prefix. `load_path` extends every writer's path by the actual load. This is the
control history needed to justify barrier ordering; memory-graph axioms must
still establish which write supplies the load's value.

## Exact dynamic occurrences

A program counter repeats in the loop. Even an entire event value might repeat,
so membership of an equal event is insufficient to identify a graph's particular
read occurrence. `run_index_prefix` locates the exact requested trace index in
its actual dispatch, including oracle advancement through skipped or waiting
dispatches. `load_prefix_at_index` then gives a prefix ending no later than that
index, with every writer's store/arrival/completion path entirely inside it.
Every event in those paths is strictly earlier than the specified load index.
No equality-based uniqueness assumption about event values is needed.

## What this does and does not establish

The inherited PTX source slice remains one complete represented CTA, one aligned
barrier site/resource/phase, explicit relaxed whole-word memory forms and no
outside interference. See `reduction-control.md` for exact pinned manual anchors
and the separate ISA9.4/sm70 feature boundary. The underlying individual-arrival
protocol remains a specialization of full-participation barrier control, not a
complete model of arbitrary warp arrival dynamics.

The history theorem is independent of address/value correctness. The data layer
supplies actual computed addresses and register-value provenance. The memory
adapter combines those with this exact trace history, source compatibility and
ordering constraints to force observations. Constructive execution, necessary
memory constraints, grounding, and whole-program output correctness remain
separate claims. No fairness or GPU hardware-conformance result follows here.

`lake build Ptx.SharedReductionHistory` passes. All 42 public declarations were
individually audited; only `propext`, `Classical.choice` and `Quot.sound` occur.
The persistent audit receipt records the exact source hash and output. Finite
instruction-case proofs use a larger elaboration recursion limit; this changes
no statement, execution definition or Lean kernel check.
