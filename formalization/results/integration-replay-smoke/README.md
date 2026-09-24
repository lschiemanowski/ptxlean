# Synthetic integration replay smoke

**Passed, with zero model calls and zero campaign calls.** This is a
coordinator-authored infrastructure test, not a third Luna instruction trial.
It adds one small module reusing the imported binary32 encoding roundtrip theorem;
it provides no evidence about a smaller model's instruction-formalization ability.

The exact base is `e00a9e51b4ab54649ce087be724f683e547f6789`. Fresh replay passed
from 21:16:29 to 21:20:12 UTC on 2026-09-23 (about 3 minutes 44 seconds):

- The pristine base's accepted-form ledger passed before patch application.
- Root source checks, clean build and dependency audit passed.
- Sixteen dependency repositories were cloned independently at pinned revisions,
  with no worker build cache or original working files copied.
- The official mathlib cache command succeeded.
- The new `PtxBinary32.ReplaySmoke` module, immutable acceptance driver and explicit
  dependency audit passed. The theorem depends only on `propext`,
  `Classical.choice` and `Quot.sound`.
- Final patch-boundary and dependency-commit/tracked-source checks passed.

The candidate root check explicitly deferred the current-file form ledger and ran
its regressions against the pristine committed fixtures. That deferral remains
recorded; this smoke does not claim renewed instruction acceptance. The new module
has no PTX instruction semantics. No task was added to the campaign ledger.

[`result.json`](result.json) summarizes the actual outcome and hashes the full
replay receipt. The original `fixture.json` records preparation state before
execution; `fresh-replay/result.json` inside the archive records the later run.
All replay commands, working directories, results and logs remain preserved,
together with the synthetic task, receipt, patch, immutable driver, coordinator
fixture script and exact runner/replayer code. Worktrees, dependency source trees
and compiled caches are deliberately excluded.

Verify every exact archive member and the archive hash with:

```sh
python3 scripts/check_worker_evidence.py formalization/results/integration-replay-smoke/evidence-manifest.json
```

The common verifier checks integrity only. It does not rerun builds or interpret
this synthetic evidence as model success, semantic fidelity or hardware behavior.

The [publication history record](../../../docs/formalization/publication-history.md)
explains the unchanged historical identities and the limits of replay from the
public checkout. Current proofs and distributed evidence remain checkable.
