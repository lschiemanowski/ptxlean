# Independent reduction entry-point review

No correctness blocker found in the reviewed five entry points and ten examples.
`Ptx/SharedReductionCorrectness.lean` SHA256:
`d524afc2a99a674419ee64d7ad71ebd062c016dbb2ce3d2a85a2155d31d0d6a8`. Fresh source elaboration passed without warnings;
all five explicit public declarations were exact-name dependency audited with
only standard Lean axioms. This snapshot includes both an emitted-output theorem
and a final-state theorem conditioned on actual leader termination.

`Ptx/SharedReductionExamples.lean` SHA256:
`918bca9a69bcbc7f4cc76d421ef0b67e863660f68430e5116ed905cfff0599d2`.
Fresh original source elaboration passed without warnings. All ten anonymous
examples were also elaborated in a temporary copy changing only their declaration
names, allowing exact-name dependency auditing. All ten audits passed, using only
`propext`, `Classical.choice` and `Quot.sound`. The actual source passed the local
forbidden-token scan. No candidate source edits were made during this review.

The examples cover wrapping addition, arbitrary old scratch/output words and
preserved tails, 32- and 64-lane instances, an incomplete barrier whose waiting
lane cannot manufacture another arrival, and a wrong global read rejected by
Sources. The 32/64 instances apply the arbitrary-input execution theorem and
kernel-check their concrete final words; they are not hardware or warp-scheduler
tests.

The stale example supplies 91 only at dispatch27, the first leader shared load.
The complete trace numbers that access28 because the completing barrier dispatch
emits both arrival and completion. The exact trace position and memory effect
are kernel-checked by `stale_at` and `stale_memory`; the fallback branch of the
extracted-occurrence definition cannot satisfy those equalities accidentally.
The resulting global storage is `[3,5,96]`, and all lanes have actually halted.
For every source/coherence choice, Ordered.Valid would force the selected read
to equal initialized input3. Since its actual effect is91, no such valid graph
exists. The interpreter is allowed to produce the candidate; memory admission
rejects it. This tests the universal memory theorem rather than forcing reads
inside the interpreter.

`completed_execution` combines the same actual fetched finite run, exact final
global/shared storage, barrier reset and all-thread halt with source/coherence
choices for that exact combined trace. It retains input/output extent and
scratch-size conditions and a separate base/RF grounding conclusion.
`emitted_access_safe` transports actual emitted effects to alignment and original
selected-arena bounds. It makes no no-fault, termination, ownership or hardware
conformance claim.

`read_contract` discharges the local arithmetic proof's read condition from
Ordered.Valid of the actual combined trace. The caller supplies neither read
agreement nor source identities. `candidate_output` applies that discharged
condition to the actual emitted global-store effect and separately derives its
immediate output address from fetched execution. It proves every such store
writes the modular input sum at slot n, for arbitrary finite schedules and read
overrides. The initial input extent is explicit. An actual store occurrence is
a premise, so the theorem alone does not promise that arbitrary scheduling emits
a store, terminates or reaches a particular final global state. The canonical
completed execution establishes nonvacuity separately.

`completed_candidate` supplies the same graph-derived read contract to
`Writeback.halted_leader`. Its initial extent includes the output slot, and its
only completion premise is that the actual lane with index zero has halted.
The reachable terminal-control invariant excludes the follower exit for that
lane and establishes output block PC1. The writeback invariant proves that this
position follows a successful actual store and that persistent global storage
is exactly `input.set n (total input n)`. Thus every other global word, including
tails, is preserved. The wrapper assumes neither a successful store, an output
occurrence, a saved result nor an expected final memory value. Its statement
ranges over arbitrary finite schedules and candidate reads admitted by the
actual combined graph. It does not assert that every schedule reaches the
completion premise; `completed_execution` supplies finite existence separately.
The reviewed writeback and terminal-control proofs preserve their invariants
through actual fetched steps, including faults and barrier releases.

The wrappers preserve the distinction between model checking and PTX semantic
fidelity: they retain the selected isolated CTA/whole-word/barrier model and do
not establish real launch geometry, hardware conformance, scheduler fairness or
a complete general dependent-memory acceptance rule. No requested result has
been placed into a new wrapper premise.
