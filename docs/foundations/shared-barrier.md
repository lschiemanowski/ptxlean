# Shared-memory publication through one barrier

Consider a block of GPU threads that each publish one word and then read a
partner's word. A CTA, or cooperative thread array, is the group launched as one
thread block. Its shared memory is storage owned by that block. A barrier makes
each thread wait until the required participants have reached the same point.
The example uses this small typed PTX program:

```ptx
st.relaxed.cta.shared.u32 [a0], r0;
bar.sync 0;
ld.relaxed.cta.shared.u32 r1, [a1];
exit;
```

Here `r0` holds the thread's input, `a0` addresses its own shared word, `a1`
addresses a selected partner's shared word, and `r1` receives the load result.
`.u32` selects one 32-bit word. `.shared` names the state space. `.cta` limits
synchronization scope to the thread block. `.relaxed` makes the memory operation
strong in PTX's classification while supplying no release/acquire ordering by
itself. The intervening barrier supplies the ordering between publication and
observation. Bare `st.shared` and `ld.shared` have different default qualifiers
and are not aliases supplied by this frontend.

The source is the pinned PTX ISA 9.4 manual, SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The relevant clauses and their interpretation are recorded in
[the independent source review](barrier-source-review.md): §§9.7.15.1,
9.7.14.7, the `ld`/`st` instruction sections, and the memory model's program
order, synchronization, causality and causality-axiom sections. This slice uses
`sm_70` or newer, where the documented memory model and explicit relaxed memory
instructions apply. This restriction does not mean `bar.sync` itself requires
such a new target.

## Representation and instruction origin

[SharedBarrierMachine](../../Ptx/SharedBarrierMachine.lean) contains the typed
instruction constructors, their exact mnemonic/token encoding, and the program.
`decode_encode` proves a round trip for the supported forms. This is not a raw
PTX parser: tokens already distinguish word registers, shared-address registers,
and resource numbers. The fixed program uses immediate barrier resource zero,
no count operand, no predicate and one unconditional instruction site.

Each thread has its own program counter, word-register function, shared-address
register function and halted bit. Word and address registers are separate typed
banks; both contain 32-bit values. The representation avoids implying that this
four-instruction fragment implements general PTX register declarations, type
checking or address conversions. All other initial register contents are arbitrary.
The only word-register write in the program is to `r1`.

`stepWith` checks whether the chosen thread is halted or already waiting. If it
can run, its actual program counter fetches the instruction from `program`.
`dispatch` executes that instruction and constructs its effects. `event_origin`
and `event_complete` connect effects in both directions: nothing is added by
relabeling a different instruction, and no dispatch effect is omitted by the
fetch wrapper. Memory effects retain thread, site, byte address, value and the
kind identifying the exact explicit shared-memory form.

A barrier request uses the configured CTA, the fetched resource operand, the
actual instruction site and the current generation. Arrivals and completion are
distinct events with that key. A waiting thread stays at the barrier; selecting
it again changes nothing and emits no duplicate arrival. The final arrival
emits arrival then completion, resets the arrival bits, increments the generation,
and advances every thread past the barrier. Reachable control invariants prove
that every thread is then at that common site. The machine does not make this
condition an assumed premise of a successful release.

## Storage and preserved inputs

[SharedBarrierProgram](../../Ptx/SharedBarrierProgram.lean) initializes thread i's
own address to `4*i`, and its partner address to `4*partner(i)`. The partner map
is arbitrary and need not be a permutation. The arena has exactly one initialized
word per participant, with arbitrary old contents. Its owner is the configured
CTA. The bound `4*n < 2^32` prevents wrapping when forming these byte addresses.

Every access checks the arena owner, four-byte alignment and word-index bounds.
`accessIndex_some` and `memory_safe` establish those checks for emitted effects.
The separate [environment adapter](../../Ptx/SharedBarrierEnvironment.lean)
translates them into the project's byte-range and ownership/accessibility
predicates. These are checks for the represented arena; they do not verify an
external allocator, launch configuration or physical device address.

The fragment represents one CTA and excludes access by any outside thread to
this allocation during the example. Shared-memory ownership alone would not
justify that restriction: PTX permits some peer-CTA accesses within a cluster.
The exclusivity restriction must remain explicit in any use of this example.

[SharedBarrierFrame](../../Ptx/SharedBarrierFrame.lean) proves that every step,
including unsuccessful and blocked steps, preserves `r0`, every address register,
and the arena owner. `run_frame` extends this to any finite schedule.
`trace_memory_fields` consequently says that every emitted memory event from the
initialized program is exactly an own-slot store of that thread's input or a
partner-slot load of its proposed observation. This result does not depend on
the specially chosen schedule below. `halted_output` also proves that any halted
thread retains its proposed observation in `r1`, while `halted_memory_counts`
proves its actual trace contains exactly one store and one load. These theorems
permit a universal completed-candidate statement over arbitrary schedules; they
do not assume the proposed observation equals the partner's input.

[SharedBarrierInvariant](../../Ptx/SharedBarrierInvariant.lean) separately proves
control facts for arbitrary schedules: program counters progress monotonically,
there is no early exit, arrivals cannot be counted twice, each store precedes its
thread's arrival, and every load has a preceding completion. Its event-count
balances connect completed control flow to the actual store and load events.
These facts let the memory proof use interleaved schedules; it need not assume
that every store globally precedes every arrival.

## Two execution modes and one concrete witness

The candidate mode supplies an optional proposed load observation for each
thread. A supplied word becomes the load's actual result and trace value, but
all instruction, control and address checks still run. This allows a separate
memory model to decide whether the proposed observations are permitted. Merely
executing a candidate does not establish that its observations are PTX-permitted.

The concrete mode supplies no overrides and reads the current arena instead.
Immediate arena updates furnish a constructive execution. They do not replace
PTX's relational memory model with a sequentially consistent interpreter.

`canonical_execution` proves an exact finite run, including its final state and
entire trace. The schedule has four rounds, each visiting every participant:

1. Store each thread's input in its own slot.
2. Execute each thread's barrier arrival; the last arrival releases the group.
3. Load each selected partner's slot.
4. Exit each thread.

There are `4*n` dispatches and `4*n+1` trace events: one store, arrival, load and
exit per thread, plus one completion. The final state has generation one, no
waiting threads, unchanged shared inputs, and every thread halted at PC three.
`candidate_completed` proves each final `r1` equals its supplied observation.
`concrete_completed` proves it equals the partner's input when loads use the
arena. These results hold for arbitrary words, including zero and maximum words.
No arithmetic or numerical approximation is performed by this example.

For example, with two threads, inputs A and B and exchanged partners, the first
round stores A in slot zero and B in slot one. After thread zero arrives it
cannot load: thread one is still missing. Thread one's arrival completes the
barrier and resumes both. Their subsequent loads return B and A respectively.
The parametric proof also supports more than one warp; the separately supplied
64-thread instance fixes two groups of 32 and chooses a partner in the other
warp. The general machine does not silently assume every target has warp size 32.

## What the memory proof adds

The [shared barrier memory graph](../../Ptx/SharedBarrierMemory.lean) contains
one initialization, one publication store and one observation load per thread.
The actual event-field proofs justify those entries. Control/history proofs
justify ordering any participating pre-barrier store before any participating
post-barrier load, retaining the common CTA/resource/generation/site identity.
The graph then proves source identity before concluding value agreement.

This separation matters. The universal result concerns candidates satisfying
the reviewed necessary PTX memory constraints and the actual barrier-derived
ordering. The concrete finite run and matching valid graph furnish existence
for this bounded program. Neither claim establishes that those graph constraints
are sufficient for every PTX program, nor that hardware implements this model.
A stale graph with the barrier ordering omitted distinguishes the role of the
synchronization from the load's mere placement later in the program text.

[SharedBarrierHistory](../../Ptx/SharedBarrierHistory.lean) makes this connection
explicit for every finite schedule in either read mode. `load_path_general` proves
that any actual
load has, for every producer, an ordered subsequence of actual events: that
producer's store, its own arrival, the common completion, and the load. A
subsequence permits arbitrary intervening events; it does not claim that these
four events were adjacent. The key is proved to be the configured CTA, resource
zero, generation zero and site one. The last producer's arrival and completion
are emitted by the same dispatch in that order, and are treated explicitly.

`completed_memory_accounting` combines the exactly-one store/load counts for
each halted participant with exact memory-event fields. Thus every relevant
actual memory event is accounted for even when stores and arrivals interleave.
These temporal and coverage proofs do not assume that proposed load observations
are memory-valid; the graph supplies that separate restriction. The history
theorem accepts arbitrary optional observations, including concrete arena reads.
`load_path` retains the specialization to arbitrary supplied candidate observations.

The chosen global order of the constructive schedule is convenient for an
existence proof. It is not a requirement on arbitrary scheduling and is not
scheduler fairness. Likewise, the memory projection's coarse proof levels
(store, arrival, completion, resumption, load) represent a partial ordering;
they are not literal timestamps in the operational trace.

## Reading the combined theorem

[SharedBarrier](../../Ptx/SharedBarrier.lean) closes the connections:

- `completed_candidate_publication` allows any finite dispatch list and any
  proposed observations. If all threads have exited and the corresponding graph
  satisfies the memory constraints, every result is its partner's input. The
  proof does not assume that observation as a premise.
- `completed_cross_origin` derives each graph barrier edge from its exact
  store/arrival/completion/load subsequence in that same completed execution.
  `completed_memory_accounting` supplies each store and load exactly once and
  rules out extra memory events. No particular interleaving is imposed.
- `all_in_scope` and `observation_scope` derive mutual scope from the actual
  CTA topology and connect the scoped observation definition to the word graph.
- `verified_execution` combines the explicit four-round run with a valid fresh
  graph, exact memory-event projection, final outputs and access safety.
  `two_warp_verified` instantiates the execution with 64 threads and partners in
  the other group of 32.

The stale graph is accepted only with the barrier edges omitted and with each
partner different from its reader. It is a distinguishing memory example, not
an execution of this program after its barrier has completed. Even when an old
word happens to equal the input numerically, the source-identity result still
excludes choosing that obsolete initialization.

## Deliberate boundaries

The fetched program visits one barrier once. Reuse is proved by the separate
protocol, not by a multiple-barrier frontend here. There are no divergent paths,
early exits, dynamic resource operands, explicit counts, mixed barrier forms,
cluster barriers, asynchronous operations, floating point or tensor operations.
The all-thread/all-warp completion theorem establishes equivalence of completion
conditions under full participation; it is not a proof of every per-warp arrival
step performed by hardware. Kernel checking validates the stated Lean theorems;
independent source review remains necessary for semantic fidelity.
