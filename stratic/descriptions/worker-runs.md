# Recorded worker runs

A worker run gives one fixed instruction task to a smaller model and preserves
what happened. Each task names a repository commit, allowed output paths, exact
source inputs and a prompt. The runner verifies those inputs before dispatch and
creates an isolated Git worktree, a checkout separate from the coordinator's
working files. This prevents routine worker edits from mixing with unrelated work;
it is not a claim that Git worktrees are a security boundary.

A campaign ledger records a call before the headless process starts. Failed,
interrupted and repeated calls all remain counted. Reserving a call is serialized
so simultaneous launches cannot exceed the campaign checkpoint. The same attempt
identifier cannot silently launch twice. A repair is a new recorded attempt
referring to the previous result. Exploration imposes no fixed per-task inference
or repair budget; the runner stops new dispatch at the agreed campaign checkpoint.

The selected route runs Codex headless with the requested model and existing
account authentication. No API-key fallback is introduced. The runner preserves
the exact prompt, command, task input, starting commit, process output, final
message, reported usage and proposed patch. Reported model identity is recorded
when available; the requested model name alone is not proof of the returned model.
Pinned source files cannot be allowed outputs; their hashes are checked against
the starting commit and again after the run. Allowed output paths must use their
canonical repository spelling. Untracked files are checked even when ignored by
Git, except named generated artifacts under `.lake` and `__pycache__` directories. Changes outside
the assigned paths or a changed checkout commit make the submission ineligible
for integration.

A repair can resume an explicitly selected completed attempt in the same recorded
Codex session and checkout, with new feedback. It inherits the original task,
base commit, allowed edits and pinned sources. Before dispatch, the runner checks
that the checkout still has the recorded commit and patch, that source hashes
still match, and that the selected attempt is the latest invocation using that
checkout. A lock rejects simultaneous resumes of the same checkout. An unresolved
started attempt must be investigated before continuing it. Each resumed invocation
gets a new call reservation, feedback, prompt, output, receipt and cumulative
patch; the previous attempt's records remain unchanged. The live checkout is
shared across those records, so previous patches preserve earlier results.

Process success only means the worker process completed. Mechanical proof checks,
source fidelity review and integration are separate steps. A patch is never
applied to the coordinator checkout automatically. Stored artifacts support later
inspection and checking without inference. A run left in a started state after
a crash is unresolved and still consumes its reserved call; it is not retried
without a new attempt record. Operational time, usage and assistance records are
needed alongside the count because one headless call can contain many turns.

Completed evaluation trials can be preserved as separate evidence archives. Each
manifest lists the exact bytes and hashes of all archived attempts, feedback,
ledger snapshots and replay/checker records, including failures and evaluator
repairs. The evidence checker verifies every evidence archive by default, or the
explicitly selected manifests. It checks bytes without extracting or executing
archive contents. An archive's integrity does not itself establish semantic
acceptance. Usage counters from resumed sessions remain raw; potentially
cumulative counters must not be added as though each were an independent bill.

A task may select a repository-local replay project for dependencies that belong
to a separate Lean package. Without that setting the root package is used. A
selected subproject has a pinned toolchain, package configuration and dependency
manifest recorded among the immutable task inputs. Its toolchain matches the
root package, Git dependencies name exact commits and path dependencies stay
inside the checkout. Workers still start in the repository root and receive
explicit build commands. Only the selected project's generated `.lake` directory
is exempted in addition to the root build directory; arbitrary ignored files
remain part of the edit-boundary check.

Before a provisioned dispatch, a separate preparation phase records the exact
project configuration, dependency revisions, prerequisite builds and available
cache route. Preparation performs no model invocation. The run phase checks that
this prepared checkout and its prerequisites have not changed before reserving
a campaign call. Both phases retain recoverable status and diagnostics; source
or dependency drift blocks dispatch rather than being silently reset.

When the base includes the accepted-form ledger, replay verifies that pristine
ledger before applying a candidate. Candidate root checks explicitly defer only
its current-file hash check, because an allowed instruction extension can change
a file already recorded there. The receipt exposes this deferral. All other root
checks still run, and integration requires coordinator review and a refreshed
ledger passing the ordinary strict checks. Deferral is never final acceptance.

A task can require a local-only PTX manual whose digest is bound to a committed
source manifest included among the task's immutable inputs. Preparation copies
only those verified bytes into an ignored local cache in the worker checkout;
it performs no implicit download. That exact input path is excluded from the
candidate patch, but its digest remains checked before and after generation and
replay. Missing or changed local input prevents dispatch. Other ignored files
remain subject to the ordinary edit-boundary check.

Public evidence archives omit raw model event transcripts, which may contain
vendor documentation returned by tools. Each omission records the original name,
byte count and digest, together with the original archive digest. Retained
receipts, candidate patches and proof checks keep their original bytes. Integrity
checking covers the distributed subset; it does not claim that an omitted
transcript can be independently inspected or a saved session resumed from that
subset. The original local records remain separate from the public artifacts.

If publication cleanup rewrites Git history, a separate commit map identifies the
original and cleaned revisions. Original tasks, receipts and Stratic reviews keep
their recorded identities: the map is not evidence that an old run checked the
new tree. Exact historical replay requires the original private history and
source inputs. The public checkout supports checking the current proofs and
distributed evidence subset, and recording new runs against its own revisions.
