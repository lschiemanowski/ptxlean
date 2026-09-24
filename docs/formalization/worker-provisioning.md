# Preparing and dispatching a worker project

`scripts/worker_provision.py` separates prerequisite setup from a counted model
invocation. Preparation and retry perform no inference. Run dispatches through
the existing `worker_run.dispatch`, retaining its account-authenticated Codex
route, removal of API-key environment variables, checkpoint of 200 reserved
calls, capture of failed/interrupted calls and independent acceptance boundary.
No attempt is automatically integrated.

The task still uses schema version 1. It pins its exact base commit and immutable
source files. For this provisioning route, `sources` must additionally contain
`lean-toolchain`, `lakefile.toml` and `lake-manifest.json` from the root commit.
A `replay_project` subproject pins the same three files at its own path and shares
the root's release toolchain. Git dependency revisions are exact commits.
Subproject path dependencies currently may name only the repository root, whose
package must have no dependencies. Root provisioning supports exact Git
manifest dependencies, but no path dependencies. Legacy direct-run and replay
tasks retain their existing validation behavior; old receipts are not rewritten.

To prepare a fresh attempt, name the prerequisite modules that already exist at
the task base. Names after `--module` are Lean module names, not shell commands.
Omitting them runs the selected package's default Lake build.

```sh
python3 scripts/worker_provision.py prepare formalization/tasks/TASK.json \
  --campaign .formalization-runs/luna --attempt TASK-001 \
  --module PtxBinary32Error
```

For a root-package task, a suitable prerequisite might instead be `Ptx`. The
selected project's cwd controls `lake build`; model dispatch still starts at the
repository root, so the task prompt must give correct subproject build commands.

Preparation creates the attempt and isolated Git worktree, preserves exact task
and prompt files, and copies the three coordinator helper scripts. It records a
plan before running setup commands. Dependencies are independent clones of the
coordinator's available local Git objects, checked out at the pinned revisions.
The clone does not copy dirty working-tree files or `.lake` artifacts, does not
share object hard links, and dissociates borrowed object stores. The local source
repository may be a symlink; destinations must be real independent checkouts.
Recorded origin URLs must continue to match the manifest.

The mathlib dependency, if present, uses `lake exe cache get`. Its exit status is
recorded. A failed official cache download permits the subsequent source build;
it does not itself make a required build successful. There is no alternative
cache-copy route. Root/subproject builds and all dependency build directories
are hashed after required builds pass. A resumed preparation may keep its own
existing verified dependency checkouts and build outputs, which are newly
recorded; these artifacts are never reused by independent fresh replay.

Only a ready attempt can run:

```sh
python3 scripts/worker_provision.py run \
  --campaign .formalization-runs/luna --attempt TASK-001
```

Run rechecks the ready-manifest hash, plan, task, prompt, saved helper versions,
exact initial patch and immutable task sources. It checks each dependency's
revision, origin, independent metadata and tracked/nonbuild untracked source
cleanliness, all recorded build-artifact bytes, and reported Lean/Lake versions.
It checks source and artifact state again after the version probes return.
Revalidation happens under the ordinary checkout lock. Only then does normal
dispatch reserve a campaign call. `run --codex PATH` retains the runner's explicit
executable override, useful for offline fake-process tests.

A same-session repair is prepared as a new attempt:

```sh
python3 scripts/worker_provision.py prepare \
  --campaign .formalization-runs/luna --attempt TASK-002 \
  --resume-from TASK-001 --feedback /tmp/TASK-feedback.md \
  --module PtxBinary32Error
python3 scripts/worker_provision.py run \
  --campaign .formalization-runs/luna --attempt TASK-002
```

It inherits the parent task, checkout and session. Parent task/receipt/event/patch
bytes are pinned. The original resume preflight runs both at preparation and
again before dispatch, checking that the parent is still the latest completed
invocation using that checkout. A separately completed repair makes an older
prepared repair stale even when its patch happens to be identical. Earlier
attempt records remain unchanged.

The attempt's principal records are:

| Record | Meaning |
| --- | --- |
| `plan.json` | Task/base/project/modules, helper hashes, prompt and repair-parent pins |
| `provisioner/*.py` | Exact helper source used for preparation and dispatch |
| `preparation.json` | Persisted setup phases, command states, logs and ready hash |
| `prepared.patch` | Exact candidate state allowed at the dispatch boundary |
| `phase-*.log` | Preserved command output, with hashes in command records |
| `ready.json` | Frozen successful preparation manifest and artifact hashes |
| `run-check-*.json` | Each run validation outcome, including rejected checks |
| `run.json` | Dispatch transition state; it prevents silently repeating a dispatch |
| `receipt.json` | Normal worker receipt, referencing the ready-manifest hash |

A failed or interrupted preparation can be retried without a model call:

```sh
python3 scripts/worker_provision.py retry \
  --campaign .formalization-runs/luna --attempt TASK-001
```

Retry appends a phase; it does not overwrite old command logs. It verifies the
same plan, helpers, source/candidate bytes and any existing exact dependency
checkout. It never resets dirty sources or deletes an incomplete clone. Such
failures require inspection and a new attempt if the recorded checkout cannot
be verified. A ready or already-dispatched attempt cannot be prepared again.
An unresolved dispatch remains a recorded investigation obligation; it is not
retried under the same identifier. Preparation failures and rejected run checks
consume no invocation, but every dispatched failed/interrupted process retains
its reservation. If the campaign checkpoint refuses dispatch, no process starts.

Dependencies are checked after the worker process too, including interrupted
calls that produced receipts. A changed dependency makes the candidate ineligible
for review. Normal source/allowed-edit boundary checks still run in the original
runner. The shared `worker_project.py` helper also serves independent replay;
replay retains fresh dependency clones and an exact helper copy/hash of its own.

Offline tests use real local Git repositories/worktrees, fake Lean/Lake programs
and a fake headless executable. They make no inference or network calls. Run:

```sh
python3 -m unittest discover -s tests -p 'test_worker*.py'
```

These tests establish workflow behavior and drift rejection, not PTX fidelity
or candidate proof acceptance. A Git worktree is not a security sandbox. A ready
manifest records bytes and provenance, not a semantic endorsement of compiled
artifacts; independent replay, proof dependency checks and source review remain
necessary.
