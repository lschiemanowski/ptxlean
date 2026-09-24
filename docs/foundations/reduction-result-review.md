# Independent reduction result and writeback review

Outcome: **no blocker found** in the arithmetic and persistent-writeback proofs
or their stated assumptions. This review independently inspected the two modules
written by the reduction-program author. It includes fresh elaboration of both
source files and a fresh enumeration and dependency audit of all 23 public
declarations. It does not substitute for independent review of the loop/history
foundations: those were written by this reviewer and are reviewed separately by
the reduction-program author.

Reviewed source hashes (SHA-256):

- `Ptx/SharedReductionResult.lean`: `b792077aac21e72045d84d367df4b75ed03aed06923f234425d2677b25951646`
- `Ptx/SharedReductionWriteback.lean`: `723eaf88f12dc622c19d3e00bfa4bef57098abd5aa6f3cb64b540c0c4355ec2d`

The hashes were checked before and after elaboration and were unchanged.

## Arithmetic and actual instruction boundaries

The accumulator invariant distinguishes the instruction boundaries correctly.
At loop program counters 0, 1, 2, 3, 6 and 7, the accumulator contains the prefix
indexed by `n - counter.toNat`. At counters 4 and 5 it already includes the next
word, although the counter has not yet been decremented. At counter 3, the load
has supplied that next input in register 2. Initialization constrains the
accumulator only after the actual move that writes zero. Initial register and
predicate banks remain arbitrary.

`Shape` is an explicit arithmetic interface, not a new assumption about
initialized executions. `shape_of_loop` obtains every field from the separately
proved reachable loop invariant: counter bounds, positivity, branch predicate,
zero at the loop-exit branch, and the actual pointer at the load. The counter
subtraction proof uses positivity to exclude unsigned underflow. `total_succ`
uses the actual list prefix and ordinary `Word` addition, which is addition
modulo 2^32; this is not a claim about unbounded natural sums.

`observed_value` constructs the memory event emitted by the actual fetched load
and identifies the value installed in its destination register. Both candidate
read overrides and the concrete arena fallback are covered by `reads.getD`.
The output theorem similarly inverts the fetched global store and obtains its
value from the actual pre-state accumulator. It cannot substitute a mathematical
sum for an unrelated emitted store.

## Assumptions and the memory boundary

The intermediate `ReadContract` really does require the input value at every
actual shared-load input slot. It is therefore a memory obligation, not an
independent proof of read freshness. The module names and documentation make
that obligation explicit. Inspection of the separately authored
`SharedReductionCorrectness.read_contract` confirmed that the final composition
obtains it from `Memory.run_shared_load_member_value` under the combined ordered
memory graph; `candidate_output` and `completed_candidate` pass the derived
contract rather than requesting fresh read values from the caller. This review
checks that composition boundary, not the complete internals of the memory
source-forcing proof.

The arithmetic theorem needs `n ≤ input.length` so every prefix input is present.
The persistent-memory theorem needs the stronger `n < input.length`, because
slot `n` is the output slot in the same supplied global arena. These are storage
bounds, not expected-output premises. No scratch-size premise is hidden: an
undersized scratch arena can fault and fail to complete. Existence and safety
are separate results.

## Persistent memory and completion

`Writeback.Invariant` states that global memory is either the initial arena or
its exact one-slot update. Its second clause connects output program counter 1
to the successful store. The proof derives the output address's exact arena
index from the non-wrapping configuration bound and storage extent, uses the
actual store's returned memory, and preserves the equation through every other
instruction and thread step. The list update equation retains every other word,
including any extra tail.

`Writeback.halted_leader` assumes the actual lane-zero thread has halted. It uses
the separately proved terminal-position theorem to obtain output block/program
counter 1, then derives the persistent memory equation. It assumes neither an
output event, a successful store, nor the desired final contents. It does not
claim fairness or termination for arbitrary schedules. Candidate observations,
finite scheduling, and incoming register banks remain universally quantified.

These results retain the surrounding fixed-program, isolated-arena and target
qualification boundaries. In particular, the arithmetic proofs do not establish
hardware conformance, general PTX memory sufficiency, or semantics for outside
interference.

## Verification evidence

Pinned Lean toolchain: `leanprover/lean4:v4.34.0`.

Commands completed successfully:

```text
lake env lean Ptx/SharedReductionResult.lean
lake env lean Ptx/SharedReductionWriteback.lean
lake env lean /tmp/reduction-result-independent-audit.lean
```

Both source elaborations exited 0 without diagnostics. The audit driver was
independently generated from every public `def` and `theorem` declaration in the
two sources, rather than reusing the author's list. The 16 result and 7 writeback
declarations use only the standard logical axioms `propext`, `Classical.choice`
and `Quot.sound` where required; none depend on `sorryAx` or a new unchecked
axiom. No source modifications were made during this review.

Temporary detailed evidence: `/tmp/reduction-result-independent-public.json`,
`/tmp/reduction-result-independent-audit.lean`,
`/tmp/reduction-result-independent-audit.log`,
`/tmp/reduction-result-independent-elab.log` and
`/tmp/reduction-writeback-independent-elab.log`. The exact dependency output is
also retained below so the review does not rely on those temporary files.

```text
'Ptx.Scalar.SharedReduction.Machine.ResultProof.ReadContract' depends on axioms: [propext]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.readContract_append' depends on axioms: [propext]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.progress' does not depend on any axioms
'Ptx.Scalar.SharedReduction.Machine.ResultProof.LaneInvariant' depends on axioms: [propext]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.Invariant' depends on axioms: [propext]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.initial' depends on axioms: [propext]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.total_succ' depends on axioms: [propext, Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.observed_value' depends on axioms: [propext, Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.Shape' does not depend on any axioms
'Ptx.Scalar.SharedReduction.Machine.ResultProof.step_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.step_global_store_sum' depends on axioms: [propext, Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.shape_of_loop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.runWith_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.runWith_global_store_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.ResultProof.global_store_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.Writeback.Invariant' does not depend on any axioms
'Ptx.Scalar.SharedReduction.Machine.Writeback.initial' does not depend on any axioms
'Ptx.Scalar.SharedReduction.Machine.Writeback.step_preserves' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.Writeback.runWith_preserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.Writeback.reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.Writeback.output_reached' depends on axioms: [propext, Classical.choice, Quot.sound]
'Ptx.Scalar.SharedReduction.Machine.Writeback.halted_leader' depends on axioms: [propext, Classical.choice, Quot.sound]

```
