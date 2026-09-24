# bitwise32 delegated trial

The selected forms are `and.b32`, `or.b32`, `xor.b32`.
The exact final Luna patch passed fresh replay, independent v3 assertions and
an audit of all 30 public declarations. Acceptance also required
[coordinator source and statement review](../../../docs/formalization/bitwise-leaves-review.md).
This took 1 recorded Luna invocation(s); evaluator corrections are recorded
separately. It is assisted development, not a held-out success-rate measurement.

The archive retains all attempts (including incomplete proofs), repair feedback,
receipts, patches, evaluator versions and final fresh replay. Its manifest binds
every retained byte and identifies omitted raw event transcripts. No vendor
manual is distributed. The base commit belongs to the cleaned project history;
exact replay needs that commit and the hash-checked local manual, not the private
pre-publication history. Candidate regeneration can differ.

Use the current project check to rebuild integrated proofs:

```sh
bash scripts/check.sh
lake env lean formalization/checks/bitwise32-v3.lean
python3 scripts/check_worker_evidence.py formalization/results/bitwise32/evidence-manifest.json
```

The [reviewer pilot](../reviewer-pilot/README.md) retains the separate advisory
model-review outcomes and their limitations. Model approval is not proof or
semantic acceptance. Raw model logs and any vendor-bearing responses remain local.
