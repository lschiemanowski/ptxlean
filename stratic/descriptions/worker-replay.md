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
