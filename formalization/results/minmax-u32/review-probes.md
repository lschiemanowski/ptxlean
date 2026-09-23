# Offline min/max review probes

The final run detected both deliberately planted defects while the unchanged
candidate passed. Every faulty candidate first compiled its own instruction
module and proofs. Detection then required failure of the independent driver at
exactly the expected assertions, with Lean reporting that the asserted proposition
is false. No model calls were made.

| Candidate | Own module and proofs | Independent checks | Interpretation |
| --- | --- | --- | --- |
| Unchanged minmax-003 | pass | pass | Positive control |
| Remove `max.u32` from `supportedMnemonic` only | pass | 2 expected failures | Wrong malformed-input classification detected |
| Exchange min/max text meanings, encoder bindings and worker decoder examples | pass | 4 expected failures | Wrong instruction meaning detected despite internally consistent proofs and round trip |

The selected candidate is the saved minmax-003 patch on base
`90e3ef657b6b336ad4c8a915930ec33a521f82f7`. The archive preserves the task,
source hash, exact patch, independent driver, harness, mutation diffs and every
command's stdout/stderr. The pinned toolchain is Lean 4.33.0. This probes two
hand-designed errors in one candidate; it does not estimate a general detection
rate, establish full semantic fidelity or independently constitute acceptance.

## First run: evaluator defect retained

`review-probes-v1/report.json` has outcome `fail`, with its mutation classified
`inconclusive`. Its unchanged control passed and its first faulty candidate built.
The driver rejected the two affected assertions, but reported a missing equality
decision instance for `Except`, rather than a checked false proposition. The
harness refused to count that as semantic detection. The initial harness also
used blank lines to delimit assertions; consecutive examples made its attribution
regions overlap. That run stopped before the second mutant. Its complete files
and exact harness are preserved.

The coordinator added a checked derived `DecidableEq` instance for `Except` and
raised the instance-search size limit in the acceptance driver. No assertions
changed. The harness now stops an assertion region at the next example as well
as at a blank line. `review-probes-v2/report.json` records the fresh complete run
with these changes. The two expected malformed-max assertions and four expected
encode/decode assertions all failed with `decide` proving their propositions false.
The report gives exact diagnostic line numbers and the driver hash; the corrected
checks were not retroactively attributed to the first run.

## Run and replay

The completed run used:

```sh
python3 scripts/check_minmax_mutations.py \
  --task .formalization-runs/luna/attempts/minmax-003/task.json \
  --patch .formalization-runs/luna/attempts/minmax-003/candidate.patch \
  --driver formalization/checks/minmax-u32.lean \
  --output formalization/results/minmax-u32/review-probes-v2
```

To replay the exact archived harness and inputs, use fresh output and worktree
paths. For example, from the repository root:

```sh
python3 formalization/results/minmax-u32/review-probes-v2/harness.py \
  --root . \
  --task formalization/results/minmax-u32/review-probes-v2/task.json \
  --patch formalization/results/minmax-u32/review-probes-v2/candidate.patch \
  --driver formalization/results/minmax-u32/review-probes-v2/acceptance.lean \
  --output /tmp/ptxlean-minmax-probes-replay \
  --worktree .formalization-runs/review-probes/replay
```

Both paths must not already exist. The script never overwrites an earlier report
or removes a checkout. It creates one new detached checkout at the task's pinned
base, verifies the source hash, applies the saved patch, and restores the original
candidate contents between cases. Each case runs:

```sh
lake build Ptx.IntegerMinMax
lake env lean /absolute/path/to/copied/acceptance.lean
```

It records the actual absolute paths and exit statuses. A failed positive control,
failed mutant build, unexpected driver error, missing expected rejection, or
interruption does not count as detecting a semantic defect. Retained checkouts
are working artifacts; neither the original worker checkout nor the main source
tree is mutated.

## Report schema

`ptxlean.minmax-review-probes/v1` records:

- `base_commit`, `candidate_patch_sha256`, `task_sha256`, `driver_sha256`,
  `script_sha256`, `sources`, `candidate_files`, `lean_toolchain`: exact inputs and
  toolchain. The first report predates the explicit toolchain field; its base
  commit still pins the same toolchain.
- `invocation`, `invocation_cwd`, `worktree`, timestamps and `commands`: execution
  provenance. Each command retains its arguments, directory, return code and
  separate stdout/stderr files. The first report predates the invocation fields.
- `cases`: control or mutation identifier, mutation diff/hash, changed-file
  before/after hashes, module and driver return codes, expected assertion ranges,
  observed diagnostics and outcome (`pass`, `detected` or `inconclusive`).
- `outcome`: `pass` only if the control and both intended detections meet all
  gates; otherwise `fail` or an interrupted `incomplete`. This is the probe-suite
  outcome, not submission acceptance.
- `model_calls: 0`, `limits`, and `artifacts`: scope qualifier and SHA256 of every
  saved evidence file except the report itself.

The known defects were designed by the coordinator and incorporated after
inspecting the candidate. They are evaluation development data, not held-out
worker tasks or evidence that a model independently found these errors.
