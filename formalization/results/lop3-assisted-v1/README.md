# Assisted LOP3 completion

**Plain `lop3.b32` is accepted.** One additional Luna headless call completed the
prior candidate using the new shared proof support. Fresh replay passed both
unchanged acceptance drivers and the complete public-definition/proof dependency
audit. The independent GLM review accepted the candidate without findings, and
coordinator inspection confirmed its source interpretation and theorem boundaries.
The accepted-form ledger now records 24 selected forms.

This is recovery on a known task, not a held-out evaluation. The original
[three-call failure](../lop3/README.md) and [pilot report](../derived-v1/README.md)
remain unchanged. Across that pilot and this continuation, LOP3 used four calls;
it did not succeed on its original first attempt.

## Assistance and exact change

The base is `73207f78f06213066c8f8d06951f0900d7d291ad`. The new task supplies the
exact old `lop3-003` patch and five generic theorems in `Ptx/BitVecProof.lean`:
conditional bit observations, preservation of an unsigned value on widening, and
the two conversion round trips. Narrowing then widening explicitly requires that
the value fit in the smaller width. Worked examples cover conditional AND,
complement, an eight-bit immediate in a 32-bit word, zero width and the boundary
values 255 and 256. These are coordinator-authored proofs and instruction;
they must count as assistance.

The coordinator also identified a malformed private helper in the old candidate:
its unparenthesized Boolean right-hand side did not state the intended equality.
This was not simply difficulty finding a proof of a valid statement. The new
helper makes that equality explicit and proves it for arbitrary widths and indices.
The original *public* contract, all eighteen universal obligations and both drivers
remain byte-for-byte unchanged. No instruction-specific computation or complete
LOP3 proof script was newly supplied by the coordinator.

Luna retained its original eight-minterm computation, execution definitions and
decoder. It imported the support module, repaired the private helper's statement,
and completed both decoder proofs. The `compute_bit` proof then checked with its
existing Boolean case analysis. The accepted module is byte-identical to the
saved worker candidate; the coordinator made no edits to it.

The single new invocation took about 165 seconds and contained **ten failed
build commands before the successful build**. No follow-up worker call or new
feedback message was needed in this continuation. A one-call success therefore
does not mean a first-try proof. The worker left harmless unused-simplification
and deprecated-rewrite warnings; these were retained with the exact candidate.

The recorded commands read the supplied contract, old candidate, helper and guide,
and checked the manual hash. They do not show a new read of its source section.
The coordinator independently reread that section and reviewed the candidate;
the advisory reviewer also received the pinned source passages. This result is
not evidence of independent source interpretation by Luna. Historical reference
fixtures were available in repository archives, but were excluded by the task's
instructions; the recorded commands show no inspection of them. This is not an
isolated or closed-book evaluation.

## Review and proof evidence

The GLM request used the existing v4 route and frozen settings, with the shared
helper included as supporting code. It returned `accept` in about 27 seconds and
reported **$0.00610885**. No retry, timeout or fallback occurred. That is reported
OpenRouter cost, not the cost of Codex subscription usage or coordinator work.
The model opinion is advisory; it neither checks Lean proofs nor authorizes
integration on its own.

Coordinator source review checked the table-index weights 4, 2, 1, immediate-only
range 0..255, PTX 4.3 / SM50 introduction conditions, the formal choice of ISA
exactly 9.4, guards, aliases, ordered reads, frame properties and decoder shape.
The selected form has no predicate result or discarded word destination. Both
qualified variants remain unsupported. Proof inspection checked that no result,
existence or decoder conclusion is hidden in a premise. The original acceptance
drivers check the corresponding arbitrary-input theorem signatures and concrete
boundary cases; a clean replay checked the exact patch at its recorded base.

[Source review](../../../docs/formalization/lop3-assisted-source-review.md) states
the limitations in detail. This does not establish raw-module validity, full ISA
coverage or GPU conformance. Adding the family to the existing catalog preserves
its result relation directly; it does not redefine the shared execution model.

## Provenance and preparation effort

`run.json` retains worker and reviewer receipts, hashes, token usage and build
counts. The CLI reported the requested model as `gpt-6-luna` but did not independently
return a model identity. No dollar conversion of its token usage is claimed.
`effort.json` records wall intervals through archive assembly, including waits;
it excludes later integration/checking/commit work and does not measure attention.

The archive retains the task, prompt, patch, provisioning, receipt, fresh replay,
filtered campaign ledger, exact delta from the previous candidate, worker command
summary and toolkit build/example/audit logs. Initial toolkit wrapper proof
errors were corrected before the frozen commit. The original trial's reference
fixture preparation is prior work and is not erased from the accounting.
Raw model events and vendor-bearing review responses stay local, with hashes
retained publicly. No NVIDIA manual text is distributed.

The result shows that this particular failure was recoverable with reusable
support and explicit diagnosis. It does not isolate which assistance caused the
success, establish transfer to unseen instructions, or demonstrate lower total
coordinator effort. Those questions require a subsequent fresh task.

## Recheck without model calls

With the pinned toolchain and local manual cache described in the root README:

```sh
bash scripts/check.sh
lake env lean examples/bitvector_proofs.lean
lake env lean formalization/checks/lop3-v1.lean
lake env lean formalization/checks/lop3-concrete-v1.lean
```

For the historical candidate, extract `worker-evidence.tar.gz`, create a detached
worktree at the acceptance record's `base_commit`, apply
`attempts/lop3-assisted-001/candidate.patch`, and use the commands in
`replays/lop3-assisted-001/result.json`. The fresh replay and its logs are retained;
rerunning proofs needs no new inference call.
