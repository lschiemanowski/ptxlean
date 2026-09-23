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
