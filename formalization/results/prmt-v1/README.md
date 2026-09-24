# Plain PRMT fresh-family trial

**Plain `prmt.b32` is accepted.** Luna completed the new family in one headless
invocation, with no follow-up feedback, new instruction-specific proof hints, or
coordinator edits to the candidate. Fresh replay passed the eighteen frozen
universal obligations, the independent concrete driver and the complete public
definition/proof dependency audit. Independent GLM source review accepted the
exact candidate, and coordinator source/statement inspection found no blocker.
The accepted-form ledger now contains 25 selected forms.

This is one successful fresh-family task under a fully supplied semantic law.
It does not establish a general success rate, independent PTX interpretation,
lower coordinator cost or a causal benefit from the new helper toolkit.

## What was supplied and what was reused

The base is `d63eb04e48c34c99f9802d1428a7b56d7c3b48c3`. The coordinator froze the
exact output-bit law, common execution interfaces, target and decoder contract,
and both acceptance drivers. No computation body was supplied. Nevertheless,
the output law determines every bit, so the worker's semantic design freedom is
limited by that complete specification.

The existing `Ptx.BitVecProof` module, its guide/examples and accepted leaf modules
were available unchanged. The command record shows that Luna read the toolkit
and several existing leaves, especially BFI, and reused their per-bit word
construction and observation-proof pattern. The candidate imports the toolkit
but does **not explicitly invoke any of its five helper lemmas**. This is evidence
that the broader supplied-contract/template workflow worked on this task;
it does not demonstrate that those lemmas caused or were necessary for success.
The private PRMT reference and three faulty variants were excluded from the
worker base and task inputs; they were archived after the worker finished.

The worker commands read the contract and checked the manual's hash, but do not
show a read of the manual section. Source fidelity therefore rests on the
coordinator's source-derived contract and separate source reviews, not a claim
that Luna independently interpreted the source. The coordinator made no
post-generation edits to the accepted module.

## Initial outcome and internal repairs

The initial invocation, campaign call 30, completed in about **131 seconds**.
Its saved patch and receipt were captured before any possible repair feedback;
none was needed. Within that call there was one failed module build, followed by
a successful build and both successful drivers. The worker also corrected a
failed audit-command invocation (`lean -` was not accepted as a file input).
It then audited its exported declarations successfully. One-call success does
not mean first-build success or error-free tool use.

The computation constructs its result from 32 Boolean observations. For each
output byte it selects one of eight input bytes, then copies either that byte's
corresponding bit or its sign bit. The full 32-bit control remains an ordinary
word operand; upper sixteen bits have no effect. Guards, source/destination
aliases, frame properties, fetched instruction origin and typed decoding reuse
the existing Pure32 mechanism. All six specialized modes remain excluded.

## Independent checks and review

Coordinator preflight used a complete private reference and a separate byte-level
integer oracle. Concrete examples cover every one of the sixteen selector codes
at each of the four output positions, ordinary byte order, sign boundaries,
nonzero upper control bits, control registers and immediates, malformed operands,
excluded modes, targets and guards. The universal driver fixes arbitrary-input
statements rather than merely checking examples.

Three faults were seeded into the private reference, each with its own matching
proofs: reversed source words, omitted sign replication and omitted four-bit
selector masking. All three compiled and passed dependency audits, but both
acceptance drivers rejected them. A subsequent offline reproduction of all four
cases passed. This supports the checks' ability to detect these particular faults;
it does not establish completeness against all semantic mistakes.

Preflight required two checker-generation corrections before freeze: splitting
universal signatures at the outer result colon rather than a binder colon, and
making a concrete target inequality explicit for the arithmetic tactic. Neither
was a worker failure or a post-dispatch change. The coordinator also wrote the
reference proof package, oracle and mutation checks; that preparation effort is
part of the cost of this result.

The existing fixed GLM reviewer returned `accept` with no findings in about
97 seconds, reporting **$0.0025224**. No timeout, retry or fallback occurred.
Its target explanation used introduction-version language; the coordinator
retains the distinction between introduction in PTX 2.0 and the model's exact
ISA-9.4 predicate. Model review is advisory and separate from Lean checking.
[Source review](../../../docs/formalization/prmt-source-review.md) explains the
source ordering, control semantics and implementation boundary.

## Evidence and limits

`acceptance.json` pins the worker patch and fresh replay. `run.json` retains
receipt hashes, invocation/build counts, reported token usage, request/provider
metadata and review cost. Returned worker model identity was not independently
reported by the CLI; the requested model was `gpt-6-luna`. No dollar cost is
inferred from Codex subscription token usage. The OpenRouter amount excludes
coordinator work and subscription usage.

`effort.json` records preparation and generation/review/replay wall intervals,
including waits. These are not measurements of active attention and exclude
subsequent integration, final checks and commit. There is no controlled comparison
isolating the toolkit's contribution or demonstrating reduced preparation effort.

The archive retains the task, prompt, patch, provisioning, receipts, fresh replay,
filtered campaign ledger, worker command summary, private reference and mutants,
preflight logs, checker-generation scripts, and offline recheck outputs. Raw model
events and vendor-bearing review responses remain local, with hashes retained
publicly. No NVIDIA manual text is distributed. Kernel proof validity, source
fidelity and hardware correspondence remain separate; this result makes no raw
module, full ISA or hardware-conformance claim.

## Recheck without model calls

With the pinned toolchain and local manual cache described in the root README:

```sh
bash scripts/check.sh
lake env lean formalization/checks/prmt-v1.lean
lake env lean formalization/checks/prmt-concrete-v1.lean
python3 formalization/review/check_prmt_v1.py \
  --output .formalization-runs/prmt-v1-recheck
```

Use a fresh output directory. The last command verifies the evidence archive,
recreates the frozen base in a detached worktree, builds and audits each fixture,
checks the original drivers' hashes, and requires all three faults to fail the
unchanged drivers. It performs no inference calls. The historical candidate can
also be replayed from its archived patch and commands in
`replays/prmt-001/result.json`.
