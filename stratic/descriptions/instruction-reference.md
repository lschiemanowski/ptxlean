# Browsable instruction reference

The HTML reference makes every instruction entry from the pinned PTX9.4
instruction-section inventory discoverable in a searchable table. A section can
contain several names, and the same name can occur in different categories.
The table keeps that context. It does not enumerate every combination of types
and options, or turn a section count into a formalization percentage.

Each accepted form links to its own page. That page explains its behavior in
project-authored words, gives operand and target restrictions, distinguishes
source review from Lean proof validity, and displays the associated Lean
computation with links to the full definitions and proofs. Source pages reproduce
project code with line anchors; the vendor manual is linked, never embedded.
Restricted core models also have pages, clearly separated from accepted leaf
forms. A missing catalog entry means no documented mapping, not proof that no
related Lean definition exists anywhere in the project.

The site works as ordinary static files without remote scripts, fonts, a build
service or a required web server. Search and status filtering enhance the table;
all entries remain available without JavaScript. It can be rebuilt deterministically
from the checked inventory, accepted-form ledger, explicit restricted-model mapping
and current project Lean sources. A stale output, missing mapping or stale accepted
source hash must fail the documentation check rather than silently show old code.

