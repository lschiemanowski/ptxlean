# Preparing a pinned worker project

Preparation creates a recorded attempt before any model runs. A fresh attempt
uses an isolated checkout of its exact task commit. A repair uses the latest
completed recorded invocation's checkout and session, with explicit feedback.
Both retain the original task, allowed edits and immutable source hashes.
Preparation itself consumes no campaign invocation; actual dispatch still uses
the existing serialized reservation and its 200-call checkpoint.

The selected project is the repository root or the task's explicitly named
local subproject. Provisioning requires the root toolchain, TOML package file
and dependency manifest as immutable committed inputs, even for a root task.
A subproject also pins those three files and shares the root's release toolchain.
Git dependencies name exact commits; supported path dependencies remain within
the checkout. These stronger provisioning requirements do not change older
recorded tasks or bypass their existing replay checks.

Dependency setup uses independent local Git clones at the manifest revisions.
The coordinator's local repository supplies Git objects, not its working edits
or compiled files; a source repository may be reached through a symbolic link.
Destination dependency paths cannot use symbolic links. The official mathlib
cache command is the only cache acquisition route. Its failure is recorded and
permits a source build. Named prerequisite modules are built in the selected
project; a failed required build leaves preparation unsuccessful.

The preparation record pins the task, base, prompt, feedback where applicable,
initial candidate patch, project inputs, dependency checkout identities, command
logs, tool versions and prerequisite build artifacts. Commands have persisted
started and finished states. A retry appends a preparation phase and preserves
previous logs. It can reuse verified exact dependency checkouts, but cannot
silently reset modified sources or erase a partially understood failed checkout.
Interrupted or failed setup remains visible even if a later retry succeeds.

Run is a separate command. Under the same checkout lock used by normal repairs,
it verifies the ready manifest and task, rechecks the exact candidate patch and
all immutable source inputs, checks dependency and prerequisite artifact drift,
and validates that a repair's parent is still the latest completed invocation.
Only then can the ordinary headless runner reserve and launch one call. Failed
preparation or failed revalidation launches no model and consumes no invocation.
A second dispatch of the same attempt is rejected. An unresolved dispatch is
inspected rather than automatically repeated.

Provisioning is not proof checking or acceptance. Generated build artifacts are
prerequisites, not evidence that a candidate faithfully formalizes PTX. Normal
post-run source boundaries, independent replay, semantic review and integration
remain required. Dependencies modified during a worker run make its submission
ineligible. This workflow introduces no API-key fallback and does not make Git
worktrees a security boundary.
