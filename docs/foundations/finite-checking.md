# Finite checking and memory-order examples

The finite checker decides the existing memory-validity predicate for one fully
specified candidate graph. The outcome classifications and litmus proofs use it
to establish concrete witnesses while proving their universal claims separately.
The instruction language and fixed global/GPU/generic-proxy restrictions are
unchanged. Start with the [first study guide](guide.md) for those definitions.

## Three different completeness questions

| Claim | Checked result | Boundary |
| --- | --- | --- |
| Does the checker accept exactly valid finite graphs? | `Graph.check_iff`: `g.check = true ↔ g.Valid`, for arbitrary size and labels. | This is equivalence to our existing formal predicate, not to the entire PTX ISA. |
| Are the message-passing outcome lists exhaustive? | `acquire_outcomes` and `relaxed_outcomes`, for arbitrary u32 result words. | Every listed outcome has an admitted program execution; every admitted result lies in the list. |
| Does this model faithfully capture NVIDIA's semantics? | Source ledger and independent semantic review, supported by discriminating examples. | The original whole-word/initialization interpretations remain source arguments. No full PTX or hardware equivalence theorem has been added. |

`Graph.check` takes event labels, read sources, and a coherence relation already
chosen by its caller. It does not enumerate all choices or synthesize executions.
It also does not validate an instruction program or an allocation. The checked
`Program.Admitted` predicate supplies generated program labels and arena bounds
in each execution-existence theorem.

## Exact nonempty reachability

[`Ptx/Reachability.lean`](../../Ptx/Reachability.lean) uses a vertex-elimination
recurrence. Begin with the edge relation. Processing vertex k keeps existing
paths and adds a path a→b whenever a→k and k→b were already available. Processing
all finite vertices produces `reachable`.

The starting relation has **no automatically inserted identity edges**. A true
diagonal therefore means a genuine positive-length cycle. This distinction is
necessary for the acyclicity requirements in `Graph.Valid`.

`reachableVia_sound` translates every computed path to the existing inductive
`Path` relation. `reachableVia_trans` shows that the computed relation composes
at each processed intermediate vertex. Once all vertices have been processed,
it includes the initial edges and is transitive everywhere, so induction on an
arbitrary `Path` proves completeness. `reachable_iff` combines the directions.
There is no assumed path-length bound, acyclicity premise, or exception for cycles.
The statements cover an empty vertex type as well.

The implementation is a simple functional recurrence which can recompute
subproblems. It is suitable for these small candidates; this work establishes
no scalable runtime bound or optimized matrix implementation.

## Checking the actual validity predicate

[`Ptx/Checker.lean`](../../Ptx/Checker.lean) obtains finite decision procedures
for the existing source, coherence, and primitive relation predicates. It uses
exact reachability twice: for base order and for the per-location union.
`causeCheck` follows the existing causality definition, including its single
observation-prefix clause. It does not transitively close causality itself.

`check` tests every field of `Graph.Valid`. `check_iff` converts these finite
tests to exactly those fields using the reachability equivalences. The theorem
is sound **and** complete; rejected candidates satisfy `¬Valid` by
`check_false_iff`. Neither the original semantics nor its validity predicate was
changed to accommodate the algorithm.

A concrete proof now has the reusable shape:

```lean
example : Ptx.MessagePassing.success.Valid :=
  (Ptx.Graph.check_iff _).mp (by decide)
```

The original certificate proofs remain available as another way to establish
validity. New witnesses use the checker and kernel-checked `decide`. No native
execution result is accepted as a proof.

## Complete message-passing outcomes

[`Ptx/MessagePassingOutcomes.lean`](../../Ptx/MessagePassingOutcomes.lean) proves
both directions of the following table:

| Final flag | Final payload | Acquire consumer | Relaxed consumer |
| --- | --- | --- | --- |
| 0 | 0 | admitted | admitted |
| 0 | 7 | admitted | admitted |
| 1 | 0 | impossible | admitted |
| 1 | 7 | admitted | admitted |

`source_values` proves that *any* compatible sources force the flag into {0,1}
and the payload into {0,7}. Thus the theorem excludes all other 32-bit words;
it does not merely sample four results. The existing universal publication
proof rules out the remaining bad acquire row. Concrete checker proofs supply
all seven admitted rows, including bounds and actual final consumer registers.
`Possible` is an existence predicate for those admitted executions.

## Four source-reviewed litmus programs

[`Ptx/Litmus.lean`](../../Ptx/Litmus.lean) uses actual instruction lists,
`Program.graph`, and final register projections throughout. These are derived
examples within the restricted model, not runnable PTX modules or copies of
NVIDIA's fence-based examples.

| Namespace | Programs and proved result | Modeling error this exercises |
| --- | --- | --- |
| `StoreBuffering` | Each thread stores 1 to its own word, then reads the other's word; both reads can return 0. | Imposing global sequential consistency on the union of cross-location PO and communication would wrongly forbid this witness. |
| `SameLocation` | One thread stores 1 then reads that same word; every admitted execution reads 1, and such an execution exists. | Ignoring same-location causality or initialization order could admit a stale initial read. |
| `ReleasePair` | Producer stores payload7, releases flag1, then stores flag2 relaxed. Consumer reads flag2 relaxed, then acquires the flag, then reads payload. The final payload must be7. | Recognizing only a release instruction itself as the observed write would miss the paired-release synchronization. |
| `AcquirePair` | Producer stores payload7 and releases flag1. Consumer first reads flag1 relaxed, then acquires flag2 written by a separate relaxed writer, then reads payload. The final payload must be7. | Recognizing only observation by the acquire instruction itself would miss the paired-acquire synchronization. |

The paired-release witness has both flag reads observe the later relaxed store;
`no_direct_release_observation` proves neither observes the release itself.
The paired-acquire witness has its acquire observe the independent third
thread's store; again there is no direct release-to-acquire observation. For each witness, `pair_required` rules out every synchronization derivation
using only the corresponding direct form, while `witness_synchronizes` proves
the actual relation. These choices ensure the pair rules have substantive work
to do. The release example
also uses an acquire pair in its proof, but the separate third-thread example
is what independently exercises that rule without a direct-acquire alternative.

Both publication theorems quantify over arbitrary remaining read values, source
maps, and coherence choices satisfying validity. Each has a checked admitted
witness, an actual final-register theorem, and arena-safety results. Store
buffering establishes the both-zero witness only; this work does not claim its
complete outcome table. All instructions are finite, and the existing
`Program.all_threads_run` supplies local completion for their chosen oracles.
None of these results asserts hardware scheduling or eventual flag observation.

The relevant source clauses are [release/acquire patterns][patterns],
[synchronization][sync], [causality order][cause],
[SC-per-location][sc], and [the causality axiom][causality]. The
[source ledger](source-ledger.md) records how they specialize to this fragment.

## Regression boundaries and reproduction

[`Ptx/CheckerExamples.lean`](../../Ptx/CheckerExamples.lean) checks empty and
singleton graphs, an empty relation without identity edges, self-loops,
three-vertex cycles, and a genuine cyclic base order. Other examples reject a
read sourcing itself, mismatched source values or addresses, reflexive coherence,
and missing initialization coherence. Synthetic raw graphs are intentional:
the checker theorem applies even to inputs not generated from a program.

Run `./scripts/check.sh --clean` from the repository root for a fresh build,
source integrity checks, and the extended dependency audit. The public entry
module imports all outcome and regression modules, so a successful build checks
their proofs. See `Ptx/Audit.lean` for the exact theorem audit list. No new
unchecked axioms, proof placeholders, or paid external model calls are used.

[patterns]: ../../references/nvidia/ptx-isa-9.4/index.html#release-acquire-patterns
[sync]: ../../references/nvidia/ptx-isa-9.4/index.html#memory-synchronization
[cause]: ../../references/nvidia/ptx-isa-9.4/index.html#causality-order
[sc]: ../../references/nvidia/ptx-isa-9.4/index.html#sc-per-loc-axiom
[causality]: ../../references/nvidia/ptx-isa-9.4/index.html#causality-axiom
