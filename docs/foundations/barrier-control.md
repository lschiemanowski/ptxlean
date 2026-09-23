# A reusable barrier control protocol

`Ptx/Barrier.lean` represents arrival, waiting, completion and reuse for a fixed,
nonempty group of threads. The intended first instruction is an unconditionally
reached `bar.sync 0` in one CTA, a launched thread block, with every thread
participating and no thread exiting first. The source interpretation is recorded
in [the independent barrier source review](barrier-source-review.md).

This module is deliberately a protocol foundation. It does not fetch PTX, move
a thread's program counter, parse barrier text, read shared memory or prove
visibility. A future instruction machine must establish that its requests come
from the appropriate actual barrier instruction and must honor waiting before
allowing a later instruction to execute. Passing a plausible-looking request
to the protocol alone cannot establish those facts.

## State and identity

`Config n` fixes the CTA identity, resource number and common instruction site,
and proves that the participant count `n` is positive. Threads are `Fin n`, so
a request cannot refer to a thread outside that configured group. Resource names
are `Fin 16`, matching the sixteen resources in each CTA. This represents valid
resource identities, not a frontend supporting every barrier form or dynamically
selected identifier. The planned first frontend supports immediate resource zero.

`State n` contains a generation number and one Boolean arrival bit per thread.
A true bit means the thread is waiting in that generation. A false bit means it
is runnable under the protocol, not that a scheduler must select it. There is no
separate runnable flag that could disagree with the arrival bit. The initial state
is generation zero with all bits false. `reset g` describes the same empty arrival
set at generation `g`.

A `Key` has all four coordinates:

```text
(CTA identity, resource number, generation, common instruction site)
```

The site is a caller-supplied identity, intended to be the common program location
of the barrier. The protocol never asserts that such a site was actually fetched.
A `Request n` pairs this key with the requesting participant. Identical numeric
resources in different CTAs are different keys; so are two generations of the
same resource. A fixed `Config` only models repeated use of its common site.
Reuse at different static instruction sites needs a later site-management rule.

## One transition

`step config state request` is a pure function returning the new state, a typed
disposition and a short event list:

| Condition | State and disposition | Events |
| --- | --- | --- |
| Request key is different from the active key | unchanged; `rejectedWrongKey` | none |
| Matching key, participant already waiting | unchanged; `waiting` | none |
| New matching arrival, another participant is still missing | set this bit; `waiting` | this participant's arrival |
| New matching arrival completes the whole set | clear every bit, increment generation; `released` | this arrival, then the completed generation's completion |

The rejected disposition diagnoses misuse of this protocol interface. It does
not classify a PTX program as undefined or promise hardware fault behavior.
Likewise, waiting is an ordinary defined outcome. A repeatedly selected waiter
cannot stand in for a missing peer, and it cannot produce duplicate arrival
events. `duplicate_wait_unchanged` states exact equality of the entire result.

Arrival and completion are separate `Event n` constructors. The last arrival's
transition emits both, using the completed generation's key. Its resulting state
already belongs to the next generation. This distinction gives a later memory
account a place to connect earlier arrivals to completion and then to resumed
instructions, without putting bidirectional edges between one undifferentiated
barrier node per thread.

## What the general proofs establish

The main invariant says that a stable state is incomplete. A complete arrival
set exists as the intermediate `mark` value inside the final-arrival transition,
then immediately resets. `initial_invariant` starts the induction;
`step_invariant` preserves it for every request, including wrong-key and duplicate
requests; `reachable_invariant` applies it to every state reachable by a finite
protocol execution. It is not merely a check of selected example states.

`arrival_monotone_in_generation` says that a bit already set remains set whenever
a step retains the generation number. Clearing all bits is paired with advancing
the generation. `missing_other_blocks_release` proves that a different participant
whose bit remains clear prevents this request from releasing the barrier.
`old_generation_unchanged` rejects any request whose generation is older than the
current one. `other_cta_unchanged` rejects a foreign CTA even if it reused the
same resource number. The generic `wrong_key_unchanged` also handles wrong site,
wrong resource and future-generation requests.

`released_iff` characterizes release exactly: correct key, fresh participant and
a completed set after marking that participant. `release_resets` and
`release_all_runnable` derive the next state and all cleared waiting bits.
`arrival_event_iff` characterizes precisely when a particular keyed participant
arrival appears in the result; `completion_event_iff` does the same for completion.
These certificates are proved from `step`. They do not accept an arbitrary list
of alleged barrier events as evidence of protocol execution.

`Runs` records a finite sequence of requests and their actual `step` transitions.
The executable `run` agrees with that relation (`run_sound`, `runs_eq_run`), and
`runs_append` composes executions. `prefix_execution` constructs an increasing
participant-index schedule. Its first `k` requests set exactly the first `k` bits
until the final request releases the phase. `round_exists` constructs `n`
requests taking any reset generation to the next reset generation.
`successive_reuse` composes two such rounds into `2*n` requests advancing by two.
These proofs apply to every participant count admitted by `Config`, including
one; they do not assume an external scheduler will follow the constructed order.

## How threads and warps relate

PTX describes warp arrival as well as thread waiting. A warp is a smaller
execution group inside a CTA. `WarpPartition n w` supplies an explicit map from
each thread to one of `w` warps and requires that every reported warp has at
least one thread. Threads thereby form disjoint fibers of the map: each belongs
to exactly one represented warp.

`WarpComplete` requires every thread assigned to that warp to have arrived.
`complete_iff_all_warps` proves that all threads have arrived exactly when every
represented warp is complete. This is an equivalence of completion predicates
under the fixed no-exit participant set. It is **not** a refinement theorem for
PTX's individual-to-warp arrival dynamics, and it does not derive a hardware
warp assignment, establish that all physical warps are full, or assume a universal
warp size of 32. A concrete instruction example must justify its own launch,
warp assignment, common-site participation and no-early-exit properties.

## Source and remaining connections

The pinned PTX 9.4 §9.7.15.1 (`parallel-synchronization-and-communication-instructions-bar`)
supplies the CTA-local sixteen-resource account, omitted-count full participation,
blocking `.sync`, completion/reset and aligned-site obligations. The source's
`exit` rule is intentionally outside this no-exit protocol. The first modern
memory example targets `sm_70` or newer; this is not a claim that immediate,
count-free `bar.sync` first became available on that target.

The generation counter, Boolean arrival set and split event constructors are
representation choices. The manual does not prescribe these data structures.
The independent source review checks their intended correspondence separately
from Lean's proof checking. Memory ordering remains a separate connection: this
module contains no axiom or predicate asserting that a shared-memory read obtained
a writer's value, and no projection from its events to a memory graph is assumed.

The next instruction layer must prove actual fetch and participation, prohibit
post-barrier dispatch while waiting, preserve these events in its trace, and
connect CTA-owned shared storage to the selected load/store forms. Explicit
counts, early exits, divergent aligned barriers, mixed barrier forms, asynchronous
completion and dynamically selected resources remain unsupported.

Check the protocol and its proof dependencies with:

```sh
lake build Ptx.Barrier
```

The module imports only `Std` and was also checked directly with Lean 4.33.0 while
the project moved to Lean 4.34.0. The release audit should include the public
proof declarations listed in `barrier-control-audit.txt`.
