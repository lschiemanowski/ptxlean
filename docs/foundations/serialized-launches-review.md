# Independent serialized launch review

Source: `integration/torchlean/PtxBinary32/Sequential.lean`, SHA256
`af66e7fc85bd6f4c4d5fa7fa4cd3eb41beed49dc5e09967a6f0c4d5c6261a10d`.
No code edits were made. No semantic/proof blocker found.

## Initial state and identity

`start` explicitly sets PC zero, takes value/predicate registers from the new
seed, binds packed argument offsets into address registers below the arity, and
retains seed defaults elsewhere. Its memory comes only from the selected live
cell. No preceding launch register state is implicitly copied. “Fresh” denotes
new assembly, not different values or invented zero initialization.

`SuccessfulLaunch` checks a live selected cell, its device owner and every
argument's logical allocation identity before using their byte offsets in the
single-arena scalar model. An argument cannot name another allocation merely
because its offset would fit. Unused offsets need not be in bounds: actual
emitted accesses, rather than unused argument values, are checked by the run.
The description correctly states this distinction. This is allocation-relative
argument binding, not physical pointers or an implementation of `.param` ABI.

## Actual execution and exact storage effects

The successful transition contains an actual `Mixed.Run` of the requested
program ending in `.halted`, followed by `SequentialStorage.writeback` of exactly
that run's `final.memory`. It does not replace execution by an assumed output
predicate or allow a finite advancing prefix/fault to count as completion.

`launch_exists` takes an actual terminating run and derives the fixed-extent
writeback from its memory-length theorem. This is a meaningful constructor;
it makes no termination promise for arbitrary programs. `run_from` and
`writeback_lookup` show that the existential entry cell agrees with the actual
caller-known lookup. The internal `Classical.choose` does not select a different
initial memory: the lookup value is unique.

The writeback consequences preserve identity, owner, size, allocation metadata
and every other cell. `word_frame` preserves each location not targeted by an
actual recorded store. Its no-store premise identifies a footprint; it does not
assume the value to be preserved.

`environment_safe` derives every emitted access's current allocation check from
the actual run's safety and the checked device owner. `final_environment_safe`
uses the proved fixed extent to establish the same check after writeback. No
arbitrary chosen read values, desired final result or Graph.Valid premise are
hidden in these safety/frame conclusions.

## Lifetimes and finite chains

Absent allocation, wrong owner and wrong argument identity each exclude a
successful launch. `no_launch_after_release` applies after an arbitrary valid
storage history, including later allocations and writebacks. It does not merely
check absence in the immediately released state.

`Chain.cons` passes the actual resulting Store into the next launch. `two_iff`
exposes both real launches and their own final states/traces. Append and invariant
lemmas combine finite chains; the invariant lemma explicitly assumes a proved
per-launch preservation property and does not purport to construct launches.
`storage_history` records each successful launch as a valid storage writeback,
which permits the generic non-revival theorem to apply to the entire chain.

This reviewer authored the underlying SequentialStorage module. Its independent
review belongs to the coordinator. The present review is independent of the
author of the launch module and checks the use of that storage interface; it is
not claimed as independent authorship review of SequentialStorage itself.

## Runtime boundary

The serialized transition is an abstract synchronous contract. A real runtime
must establish completion, preceding-write visibility, lifetime continuity and
absence of interference to implement it. Those conditions are not inferred
from a PTX thread exit, device scope or standalone memory-graph validity.
There is one thread and one selected allocation per launch. No asynchronous
streams, overlapping launches, multi-allocation pointer arithmetic or combined
cross-kernel PTX memory graph is claimed. Subsequent entry snapshots are not
new physical initialization writes. The description states these limitations
accurately.

## Independent checks

Run from the pinned `integration/torchlean` project:

    lake env lean PtxBinary32/Sequential.lean
    lake env lean /tmp/sequential-independent-audit.lean

Both passed; fresh source elaboration produced no warnings. The independent
namespace-aware inventory contains all 39 explicit public definitions, types and
theorems. All 39 exact dependency reports were matched against that inventory,
including multiline reports. Only propext, Classical.choice and Quot.sound are
present. No proof hole or new unchecked axiom was found.

Evidence: `/tmp/sequential-independent-audit.log`,
`/tmp/sequential-independent-names.json`,
`/tmp/sequential-independent-elaboration.log`.
