# Replaying worker proof checks

A generated patch must be checked from its recorded source commit in a fresh
checkout. The replay uses the saved patch, not the worker's live files or compiled
artifacts. It verifies the task, patch and source hashes and checks the output
file boundary again before running the pinned project's existing checks.

Additional modules must build explicitly even when the base project's main import
does not include them yet. Coordinator-owned acceptance drivers check required
interfaces and independently chosen examples; their exact contents are copied
and hashed into the replay record. An explicit list of declarations is inspected
for logical dependencies, permitting only the project's standard Lean axioms.
The source guard also rejects proof placeholders and unchecked declarations.

Every command's output and result remain recorded, including failures. Checking
must leave the submitted source patch unchanged. A successful replay establishes
these mechanical checks only. Independent comparison with the PTX source and
review of theorem assumptions remain necessary before integration. Replaying a
patch makes no model call and does not apply it to the coordinator's checkout.

For a selected subproject, replay still checks the root package first. It then
builds the requested modules and runs contract drivers and dependency audits
from that subproject, recording each command's working directory. Package
configuration and lockfiles must remain unchanged. Dependency sources are fresh
independent Git checkouts at the manifest's exact commits, obtained from local
source repositories without reusing their compiled artifacts or writing through
symlinks into the original checkout. Missing source revisions or toolchains
produce an explicit failed prerequisite rather than a successful result. For mathlib, the normal official cache command is recorded against its pinned
source revision; cache failure remains visible and a fresh source build may
continue. Candidate, TorchLean and FloatLib builds use the new checkout. Dependency
commits and tracked files are checked after preparation and after the build;
their availability is not inferred from a worker's successful build.

An accepted-form ledger in the pristine base must pass before patch application.
Candidate root checks defer only that ledger's current-file validation and record
the deferral for coordinator revalidation. Ordinary project checks remain strict;
a successful candidate replay cannot claim renewed ledger acceptance.

A preserved synthetic smoke has exercised this path on the committed binary32
foundation in `integration/torchlean`: pristine root checks, sixteen independent
dependency checkouts, the official mathlib cache, a newly added module, an
immutable contract driver and a standard-axiom audit all passed. The new theorem
only reuses the imported encoding roundtrip. This tests replay plumbing, not a
model's ability to formalize an instruction, and consumed no model or campaign
calls. Its archive omits worktrees and compiled caches. The candidate ledger
deferral remains visible; the smoke does not confer instruction acceptance.
