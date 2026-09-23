# Running and reviewing a delegated task

The initial runner is `scripts/worker_run.py`, using Python's standard library.
It sends one recorded task to GPT-6 Luna through Codex headless and leaves its
patch for separate checking and semantic review. It does not accept or integrate
code. The full workflow is described in [Stratic](../../stratic/descriptions/model-formalization.md).

A task JSON file fixes a Git commit, exact allowed file paths, pinned source
hashes and an instruction prompt. Reference sources cannot also be worker output
paths. The worker's checkout starts at that commit even when the coordinator has
uncommitted edits. Relevant source sections and required theorem statements belong
in the task; the entire manual is not automatically pasted into the prompt.

For example, from the repository root:

```sh
python3 scripts/worker_run.py run formalization/tasks/minmax-u32-v1.json \
  --campaign .formalization-runs/luna --attempt minmax-001
python3 scripts/worker_run.py status --campaign .formalization-runs/luna
```

Attempt IDs cannot be reused, even after failure. Use a new ID for any new
invocation and keep the same campaign. The ledger reserves a call under a file
lock before dispatch. It checks back before call 201, counts failed launches,
and conservatively retains reservations after a crash. There is no per-task
inference timeout or fixed retry allowance. Existing unresolved attempts must be
inspected before another attempt is deliberately launched.

The CLI runs with `--approve-for-me`, which selects workspace-write with automatic
approval review. It cannot be combined with a separate `--sandbox` flag in the
installed CLI. User configuration is omitted for predictable worker setup, while
saved account authentication remains available. API-key environment overrides
are removed. No separately billed provider fallback is attempted. CLI invocation
semantics are documented in the [official non-interactive guide](https://learn.chatgpt.com/docs/non-interactive-mode).
Local CLI behavior is also checked with `codex exec --help` before dispatch.

Each attempt preserves `task.json`, `prompt.md`, `receipt.json`, `events.jsonl`,
`stderr.log`, `final.md` when produced, and `candidate.patch`. A fresh attempt
creates its detached worktree; repairs reuse that checkout while preserving
every earlier receipt, log and patch. The receipt includes the exact command, runner hash, starting commit,
source task hash, prompt hash, final patch hash, exit status and reported usage.
A missing reported model identity remains unknown; the requested identity is
recorded separately. Failed processes are not counted as successful formalization.
A zero exit status is still only process completion, not proof or semantic acceptance.

The post-run boundary check includes tracked changes and untracked files even
if Git ignores them, except generated `.lake` and `__pycache__` artifacts. It also
checks the checkout commit and pinned source hashes. These checks detect accidental
boundary violations; they are not a hostile-code sandbox. Git worktrees share
repository metadata. The task instructions prohibit commits and extra model calls.

Raw records and worker checkouts live in `.formalization-runs/`, excluded from
Git. Selected task prompts, receipts, logs and patches can be archived with an
evaluation report after inspection. Retain raw records; an isolated worktree or
an uncommitted output is not itself a durable release artifact. Review patches
in a separate checkout, using the pinned task base, and rerun the coordinator's
checks before integration. Rechecking a saved patch needs no inference; identical
regeneration is not promised.

## Continuing an incomplete attempt

Write explicit feedback, then select the prior attempt by ID:

```sh
python3 scripts/worker_run.py run --campaign .formalization-runs/luna \
  --attempt minmax-003 --resume-from minmax-002 --feedback /tmp/minmax-feedback.md
```

The runner retrieves the original task and the one recorded Codex session ID;
no new task file is accepted. It requires a finished prior receipt, the latest
invocation for that checkout, unchanged source hashes, and the exact previous
patch and checkout commit. A nonblocking checkout lock rejects simultaneous
resumes. A crash with an unresolved reservation requires investigation; choosing
an older attempt cannot bypass it. These checks protect normal coordination,
not against unrelated processes manually changing files during a run.

The command uses `codex exec --approve-for-me --cd WORKTREE resume` with explicit
`--ignore-user-config`, `--model gpt-6-luna`, `--json`, an output-message path,
the session ID and a prompt read from stdin. The installed resume subcommand
does not accept its own `--cd` or `--approve-for-me`; these are parent options.
This syntax was checked with `codex exec resume --help` and a parse-only invocation.

Every repair reserves another campaign call before launch, including a failed
repair. It saves `feedback.md` and a new prompt, logs, receipt and cumulative
patch against the original base. The receipt records the parent attempt, session,
previous patch hash and feedback hash. The live worktree advances, so use saved
patches to reconstruct earlier results. Changing the original task or copying an
unrecorded patch into that checkout is not a supported repair route.

A general semantic-review grader and automatic integration are not yet
implemented. Reviewer-written acceptance drivers and manual independent source
review supply the initial acceptance checks. The test suite uses fake local
workers, never a model, to exercise source mismatch, edit violations, malformed
output, failures, duplicate attempts and concurrent checkpoint reservations.
