# Funnel-shift family trial

**All four `shf.l/r.clamp/wrap.b32` forms are accepted.** One Luna invocation
completed the instruction module; it is integrated byte-for-byte without coordinator
edits or a repair invocation. Fresh replay passes all 21 original universal
obligations, corrected concrete driver v2, and every public definition/proof
dependency audit. Independent GLM semantic review returned accept, and coordinator
source/statement inspection found no candidate blocker. The ledger contains 29
selected accepted forms, not a claim of full ISA coverage.

## Initial result and checker repair

Campaign call 31 requested `gpt-6-luna` and took about 146 seconds. The runner did
not report a provider-confirmed model identity. Luna read the actual manual section,
used existing leaf templates, repaired a failed internal build, and passed the
universal driver and its own dependency audit. It then correctly reported that the
frozen concrete driver failed. Its initial result and original checker are retained.
One invocation is not first-build success or an initial all-check pass.

The coordinator's concrete checker had three defects:

- It accidentally retained 64 byte-permutation examples copied from an earlier
  task. They were unrelated to the funnel-shift contract and some were false.
- The negative target test needed an explicit natural-number inequality type
  before arithmetic automation could use it.
- Decoder equality tests used `decide`, although the error type has no required
  decidable-equality instance; direct definitional proofs suffice.

`shf-concrete-v2.lean` corrects these defects. It retains all 656 independently
calculated funnel-shift results, guards, repeated/overlapping operands, target
limits and exact spelling/operand tests. The original v1 remains intentionally
failing historical evidence. The semantic contract, universal driver and candidate
were not changed. There was no follow-up worker call or coordinator candidate repair.

Preparation cross-checked a 64-bit concatenation oracle against 32-bit shift formulas,
but did not preflight the complete Lean checker against a reference module. That
omission let the checker defects reach the worker. The correction is part of
coordinator cost, not model failure or evidence of unusually low total effort.

## What is proved and reviewed

The four universal computation equations cover every 32-bit input and count.
Clamp caps at 32 and wrap reduces modulo 32; first input is the low source half,
second the high half. Left returns the shifted high half, right the shifted low
half. The common proofs cover guard polarity, incoming reads, aliases, frames,
one-step existence, event origin and exact typed decoding. Fetched leaf steps
select ISA9.4 and numeric SM≥32; PTX3.1 is the source introduction version.

The coordinator supplied complete result equations and shared interfaces. Luna's
computation follows those equations directly. This tests proof construction and
integration under a precise supplied contract, not unsupervised semantic discovery
or an isolated productivity improvement.

Three deliberately wrong modules change their own equations alongside their
computations: source reversal, wrap-as-clamp, and clamp-at-31. All compile and
pass dependency audits, yet both the universal driver and concrete v2 reject each.
The original candidate passes. These mutation probes ran after dispatch; they were
not reference preflight before the initial worker call.

The separate GLM review took about 16 seconds and reported **$0.0057362**. No
retry, route change or timeout occurred. Its verdict was accept, with no findings.
The coordinator corrected an overgeneralization in the review explanation: at
wrapped count zero, only left returns the second source; right returns the first.
See [source review](../../../docs/formalization/shf-source-review.md). Raw model
responses and vendor-bearing source material remain local; public records contain
hashes, receipts and project-authored summaries.

## Composition example and reproduction

The coordinator separately authored `Ptx/FunnelRotation.lean`. Both directions
match Lean's standard word rotation for every runtime count, execute in place,
and have completed-execution witnesses, all-run correctness and frame proofs.
The register-only program inherits the combined-kernel ISA9.4/SM70 boundary,
which is stricter than the instruction's own floor. The example establishes no
GPU launch, raw PTX parsing or hardware conformance.

```sh
bash scripts/check.sh
lake env lean formalization/checks/shf-v1.lean
lake env lean formalization/checks/shf-concrete-v2.lean
lake env lean examples/funnel_rotation.lean
python3 formalization/review/check_shf_v1.py --output /tmp/ptx-shf-recheck
```

Use a new output directory for the mutation check. It checks the exact candidate
hash, uses the frozen base in an isolated checkout and makes no model calls.
The [study guide](../../../docs/foundations/funnel-rotation.md) explains the register
interface, expected output and theorem boundaries. Archived replay and mutation
logs record the exact checked versions. Aggregate final checks and the exact
integrated tree are recorded through Stratic.
