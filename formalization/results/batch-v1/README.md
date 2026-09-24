# Three-family generation and review trial

Luna completed three frozen tasks in one call each. All three exact patches passed
fresh replay and coordinator source/proof review; five forms entered the catalog:
`brev.b32`, `mul.hi.u32`, `mul.hi.s32`, `bfe.u32`, `bfe.s32`.
The accepted-form ledger now contains 22 selected forms, not complete ISA coverage.

| Task | Calls / feedback repairs | Worker duration | Fresh replay |
| --- | --- | --- | --- |
| Bit reversal | 1 / 0 | 100.1 seconds | Pass: 18 required theorem signatures, edge cases, 28 audited declarations |
| High-half multiplication | 1 / 0 | 107.9 seconds | Pass: same obligation/audit counts |
| Field extraction | 1 / 0 | 91.4 seconds | Pass: same obligation/audit counts |

These are recorded process durations, excluding prerequisite setup and coordinator
work. Calls 20–22 used the requested `gpt-6-luna` model through Codex headless;
the event stream did not report a model identity independently. No candidate
edits, feedback calls or checker repairs were needed after dispatch. All task
inputs derive from commit `ee4689395058b8eef9164aafb2866c6b96d88abc`.

## What the coordinator supplied

The coordinator interpreted the pinned manual, selected the restricted forms,
specified the computation definitions and eighteen universal theorem signatures,
and supplied existing completed leaves as templates. Luna implemented those
contracts and proofs. This is evidence for template-based formalization under
precise supervision, not for independent discovery of PTX semantics.

Before dispatch, separate coordinator fixtures exercised the complete acceptance
drivers. They were made by adapting existing proof templates and were excluded
from worker checkouts and pinned worker inputs. Deliberately wrong fixture
variants still compiled with their own proofs but failed concrete semantic
assertions. Draft checker issues involving signature extraction, recursion limits
and concrete target-floor proofs were fixed before freezing. Final checkers were
unchanged during generation and replay. Preflight records and fixtures are in
[the evidence archive manifest](evidence-manifest.json).

This preparation is substantial coordinator work. It is not included in worker
duration, not credited to Luna, and not a proof that the chosen definitions match
the manual. Active coordinator time was not measured. These three related pure
families do not establish end-to-end cost effectiveness or capability on memory,
concurrency, undefined behavior, multiple destinations or asynchronous work.

## What the reviewer established—and got wrong

The v4 GLM request, schema, model settings and packet construction were unchanged.
Six fresh, frozen fixture cases comprised a correct and faulty candidate for
each family. Labels, patch names, mutations and prior verdicts were absent from
the requests. All six candidates built with their own proofs; exact dependency
audits passed. The independent driver accepted each control and rejected each
fault through a false concrete assertion. These are three related pairs, not
six independent instruction families.

| Case | Actual case | Final GLM verdict | Coordinator adjudication |
| --- | --- | --- | --- |
| b01 | Extraction without masking the position | Reject | Detected the seeded fault |
| b02 | Correct reversal | Accept | Correct |
| b03 | Correct multiplication | Reject, after an interrupted first request | False rejection: wrong claim about Lean division |
| b04 | Correct extraction | Accept | Correct |
| b05 | Identity instead of reversal | Reject | Detected the seeded fault |
| b06 | Unsigned interpretation in signed multiplication | Reject, after an interrupted first request | Detected the seeded fault |

Thus GLM detected all three planted faults, accepted two controls, and falsely
rejected one control. It also reviewed each actual worker candidate separately:
reversal was accepted, multiplication was falsely rejected for the same reason
as b03, and extraction received an uncertain verdict based on unsupported concerns.
These actual-candidate reviews are separate from the six fixture cases.

The multiplication allegation was that Lean integer division truncates toward
zero. In the pinned Lean version, division by a positive denominator rounds
downward: `(-1 : Int) / (2^32 : Int) = -1`. Checked examples refute the exact
counterexamples proposed by the reviewer. The extraction report claimed that
masking and the complete computation were missing, although both modulo-256
bindings and the full body were present in the hash-verified packet. Its question
about constants was adjudicated against the explicit typed-interface contract and
the manual's general instruction/constant rules, read together with its register
state-space rule. See [source review](../../../docs/formalization/batch-v1-source-review.md).
The candidate code and task contracts were not changed to satisfy these reports.

This result supports retaining the reviewer as an additional source of findings,
with coordinator adjudication. It does not support automatically accepting or
rejecting submissions from model verdicts, or a general reviewer sensitivity
estimate. No prompt tuning was performed on these results.

## Request reliability and cost

Nine distinct packets required twelve requests: six first requests completed,
three multiplication requests were interrupted after more than ten minutes
without a completed response, and one identical-packet retry for each completed.
All attempts are retained in [reviews.json](reviews.json). The original receipt
and separate coordinator interruption record are preserved; interruption is not
scored as a semantic miss or rejection.

The runner's 300-second socket timeout did not bound total response duration.
The retries used a coordinator-managed 600-second wall-time bound. This was an
operational adaptation after observing the stalls; request bytes, runner bytes,
model and semantic review settings remained identical. A runner-enforced total
deadline remains a tooling improvement, and automatic retries were not added.

OpenRouter reported **$0.027346240 across the nine completed requests**. Billing
for the three interrupted requests is unknown; that figure is not the complete
cost of the trial. Codex usage is recorded separately in [workers.json](workers.json),
without converting subscription usage into an invented dollar cost.

## Reproduce without model calls

From the repository root, acquire the pinned manual following the README, then:

```sh
bash scripts/check.sh
lake env lean formalization/checks/brev32-v1.lean
lake env lean formalization/checks/mulhi32-v1.lean
lake env lean formalization/checks/bfe32-v1.lean
lake env lean formalization/review/batch-v1/adjudication.lean
python3 formalization/review/check_batch_v1.py \
  --output .formalization-runs/batch-review-recheck
```

Use a fresh output directory. The last command reconstructs the six exact
fixture patches, builds each, audits all public definitions/proofs and runs the
fixed semantic driver. It makes no inference call. Actual-candidate recipes are
under `formalization/review/candidates/`; reconstructing model packets requires
the local vendor manual. Regeneration can return different model output.

Each family has a separate archive of worker preparation, task, prompt, exact
patch, receipt, replay and filtered campaign ledger. The batch archive contains
preflight and fixture checks. Raw model requests, responses and event streams
stay local because they can reproduce vendor passages. Public reports use
hashes and coordinator-authored adjudications. Omitted worker event hashes remain
in each family's evidence manifest. No NVIDIA manual is distributed.
