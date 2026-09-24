# Worker-derived computation pilot

**One of two families was accepted.** Luna produced a complete `bfi.b32`
(bit-field insertion) leaf after three headless calls. Plain `lop3.b32`
(three-input Boolean logic) remained unaccepted after three calls. Each family
received two rounds of coordinator feedback. No candidate code was edited by the
coordinator, and the frozen contracts and drivers were not weakened or changed.

The accepted insertion leaf is in `Ptx/Bfi32.lean` and the reviewed pure-instruction
catalog. The accepted-form ledger now contains 23 selected forms. No LOP3 module
or accepted-form entry was added. Other widths, predicate-producing LOP3 variants,
raw-module validation, complete ISA coverage and hardware correspondence remain
outside this result.

## What was actually delegated

The [frozen protocol](../../contracts/derived-v1-protocol.md) and contracts
at base `c652f951e6759d2d5e1bb56335e511347791dc1e` supplied the common execution
interfaces and eighteen exact universal theorem statements per family. Unlike the
previous batch, the computation bodies were absent. A source-derived output-bit
law still specified every output bit for every input. This tests implementation
freedom under a precise supplied specification; it does not test unsupervised
interpretation of the PTX manual.

Luna independently chose a per-bit list construction for insertion and a sum of
Boolean minterms for LOP3. A minterm selects one of the eight combinations of
three input bits. The coordinator's private LOP3 reference used a different,
per-bit construction. The reference sources were absent from the worker base and
task inputs, and were archived only after generation.

| Family | First call | First repair | Second repair / final fresh replay |
| --- | --- | --- | --- |
| BFI | Nonexistent bit-vector constructor and operand-index proof errors | List construction chosen; observer and operand-index proof errors | Pass; integrated unchanged |
| LOP3 | Bit-observation and typed-decoder proofs fail | Same proof areas unfinished | Fail; no integration |

First and final candidates received clean, independent replay from the frozen
base. Middle failures were inspected in their worker build output, without a
separate replay. A receipt saying `completed` means the headless process finished,
not that its proofs passed. The final BFI replay checked both frozen drivers and
all public definitions/theorems for disallowed dependencies.

The two BFI feedback messages progressed from compiler/library facts to explicit
lemma names and simplification advice. The two LOP3 messages supplied a conditional
bit-observation helper statement, Boolean case-analysis advice, and a strategy
for immediate-range and decoder proofs. These were substantial proof hints;
no completed Lean proof scripts or computation bodies were supplied. The messages
and every candidate patch are retained in the per-family archives.

## Exact remaining LOP3 obligation

The last candidate still fails compilation in the conditional bit-observation
helper, the universal `compute_bit` theorem, `Text.decode_encode`, and
`Text.decode_iff`. It must prove the specified input ordering (weights 4, 2, 1)
for all 256 tables and all valid output positions, and both exact decoder
directions with the immediate range preserved. It must then pass both unchanged
drivers and the complete fresh dependency audit. A computation that appears
source-consistent is insufficient. This pilot outcome is not an impossibility
claim or a new campaign call limit.

## Independent review and adjudication

The fixed GLM reviewer received four blinded fixtures: one control and one
compiling semantic fault per family. Both controls were accepted; both faults
were rejected with the intended fault identified. The BFI fault omitted masking
the position to eight bits. The LOP3 fault swapped the first and third input's
truth-table weights. All four fixtures compiled and passed dependency audits;
only the controls passed the independent concrete checks.

The LOP3 reviewer's proposed counterexample was wrong: table `0x80` is symmetric
and does not distinguish the swap. Table `0xF0` with input bits `(1,0,0)` does.
[Lean adjudication](../../review/derived-v1/adjudication.lean) checks both the
invalid claim and its corrected replacement. Count this as explained fault
detection with an incorrect example, not a wholly correct review. Two faults and
two controls cannot establish general reviewer accuracy.

Actual candidate reviews, costs and any failed requests are recorded in
[reviews.json](reviews.json). The accepted BFI candidate received an accepting
advisory verdict, but its explanation conflated the loop offset and output bit
index in an intermediate equivalence. The source review corrects this explicitly;
the verdict alone is not a trusted derivation. The first LOP3 review exhausted its 16,384 output tokens after
453 seconds and produced no usable verdict. That is a completion failure, not
a timeout or semantic rejection. Distinct first/final LOP3 patches were reviewed;
there was no automatic retry or fallback. The final LOP3 review hit the enforced
600-second total deadline, produced no verdict, and has unknown billing. This
real request confirms that the deadline terminates a waiting call and records
a distinct failure rather than inventing a semantic result.

The total-deadline runner separately limits connection plus response reading to
600 seconds, alongside the 300-second socket inactivity timeout. Local tests cover
continuous trickling and blocked connection, failure receipts, alarm restoration,
and a later successful request. This mechanism uses a POSIX main-thread alarm;
it does not cancel provider work or guarantee known billing after interruption.
Prompt, schema, model, temperature and reasoning settings were preserved.

## Effort and evidence

[workers.json](workers.json) preserves all six invocation durations and reported
usage. Resumed-session token values may be cumulative: they are not summed into
an invented per-call bill. Codex subscription usage has no reported dollar cost
here, and returned model identities were not independently provided by the CLI.
The requested model was `gpt-6-luna` throughout.

Coordinator work included source review, two contracts, four drivers, two complete
reference proof packages, two compiling semantic mutants, draft proof/checker
repairs, a deadline implementation with regression tests, four feedback messages,
source/proof adjudication, and integration. The archived phase wall intervals
include tool waits and concurrent work; they do not measure active attention.
The earlier batch did not measure coordinator attention, so there is no supported
quantitative claim of preparation-time improvement. This trial instead exposes a
proof-engineering bottleneck under the pinned library.

The BFI and LOP3 directories retain every attempt, patch, feedback, available fresh
replay and a filtered campaign ledger. Raw worker events and vendor-bearing
review packets/responses remain local; manifests retain their hashes. This report
uses project-authored summaries. The support archive contains the preflight
fixtures and mutants, draft repairs, offline fixture checks and infrastructure
regression logs. No NVIDIA manual text is distributed.

## Recheck without model calls

With the pinned Lean toolchain and local source cache described in the root README:

```sh
bash scripts/check.sh
lake env lean formalization/checks/bfi32-v1.lean
lake env lean formalization/checks/bfi32-concrete-v1.lean
lake env lean formalization/review/derived-v1/adjudication.lean
python3 formalization/review/check_derived_v1.py \
  --output .formalization-runs/derived-v1-recheck
```

Use a fresh output directory for the fixture checker. It recreates the frozen
base in a detached worktree, checks recipe/packet/source hashes, builds and audits
all fixtures, and requires the two deliberate faults to fail the concrete driver.
It needs the pinned local manual to reconstruct packets, but makes no model calls.
The accepted BFI drivers succeed in the main project; the unaccepted LOP3 driver
has no main-project module to import.

[Source review](../../../docs/formalization/derived-v1-source-review.md) explains
the semantic interpretation and restrictions. Lean proof validity, fidelity to
the source document, advisory model review and hardware behavior remain separate.

The seven GLM requests reported **$0.032888590** in total for the six requests
with billing; the final LOP3 deadline request has unknown additional cost.
Both LOP3 requests lacked usable verdicts. Per-request providers, usage, exact
packet hashes and durations are retained in `reviews.json`. Recorded coordinator
phase durations in [effort.json](effort.json) end before final snapshot checks
and commit.
