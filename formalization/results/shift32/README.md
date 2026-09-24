# Delegated shift family

Luna implemented `shl.b32`, `shr.u32` and `shr.s32` in one headless invocation
without feedback or coordinator edits to the candidate. A fresh GLM review using
the unchanged v4 protocol accepted the fixed candidate in one call. Acceptance
also required [coordinator source/statement review](../../../docs/formalization/shift32-review.md)
and fresh Lean replay auditing all 28 public definitions and theorems.

The original immutable driver contained a proof elaboration error, and the second
version contained a tactic-scoping error. The third lifts an independently checked
word equality through the state-write function. Assertions and hypotheses were
unchanged. The archive retains all three drivers, the failed and successful
replays, exact worker patch, receipt, prompt and campaign entry. This is one
successful candidate, not a general productivity estimate; evaluator failures
are not attributed to Luna.

The source manifest and task base identify cleaned repository history. Raw model
transcripts remain local because they may contain vendor passages; the evidence
manifest identifies the omitted bytes. The separate [review receipt](review.json)
retains hashes and usage, with a coordinator-authored adjudication rather than
raw model prose. OpenRouter reported $0.001587735. Codex usage is separate.

Recheck the integrated leaf and archive without model calls:

```sh
bash scripts/check.sh
lake env lean formalization/checks/shift32-v3.lean
python3 scripts/check_worker_evidence.py formalization/results/shift32/evidence-manifest.json
```

The exact source-backed review packet is reconstructible from
`formalization/review/candidates/shift32-001.json` and its saved patch after local
acquisition of the pinned manual. A future model invocation can produce a
different response. Its verdict never authorizes integration by itself.
