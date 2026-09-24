# Independent reviewer development trial

Both requested OpenRouter models can identify genuine defects in definitions
whose Lean proofs still compile. This trial does **not** justify unattended
semantic acceptance. GLM produced more usable reports here; DeepSeek repeatedly
spent its output allowance without a completed report. Both needed coordinator
adjudication. This is a small, adaptively revised development set, not a benchmark
of general model quality.

The trial made 38 recorded requests: 19 to `deepseek/deepseek-v4.1-flash` and 19 to
`z-ai/glm-5.3-flash`. Reported inference cost totals **$0.627531379 for 37 calls**;
one timed-out DeepSeek request has unknown cost. This is not a total invoice and
does not include Codex/Luna usage. Provider identities, per-call usage, timing,
request settings and hashes are in [results.json](results.json). The complete
[invocation table](invocations.md) includes failures; no favorable retry replaces
an earlier result.

## Cases and mechanical controls

The five recipes in [the case directory](../../review/cases) fix public commit
`2e0f514a5de4409c669390f468fff2b2038b352f`, complete candidate/support files and
pinned source sections. Labels and patch filenames were omitted from model
packets. The same case packet went to both reviewers without the generating
model's conversation.

| Case | Candidate | Intended distinction |
| --- | --- | --- |
| r01 | Unchanged `selp.b32` | Correct control |
| r02 | Reversed selection and matching theorems | True selector copies the wrong source |
| r03 | Altered malformed-operand error | Recognized malformed spelling must be distinguished from unknown spelling |
| r04 | Unchanged signed min/max | Correct control |
| r05 | Increased numeric SM threshold | Excludes part of the explicitly promised target slice |

All five candidates build and pass audits of nine named declarations each.
Independent assertions pass for the controls and reject each planted defect.
These checks are recorded in [mechanical-v2/report.json](mechanical-v2/report.json),
with drivers and logs alongside it. The initial r03 driver failed because Lean
could not synthesize decidability of equality on the decoded instruction type;
that is an evaluator error, not defect detection. Its failed driver/log remain in
[mechanical](mechanical). The corrected driver checks the error using a Boolean
match. Explicit target constructors also avoid unrelated elaboration ambiguity.
The [mechanical manifest](mechanical-manifest.json) pins both sets of evidence.

## Every development round

| Round | Calls | Changes | DeepSeek valid reports | GLM valid reports |
| --- | ---: | --- | ---: | ---: |
| v1 | 10 | JSON packet; high reasoning; 12,288 output tokens | 2/5 | 4/5 |
| v2 | 10 | Full files rendered as numbered Lean blocks; high reasoning; 24,576 output tokens | 0/5 | 2/5 |
| v3 | 10 | Schema also in prompt; medium reasoning; 16,384 output tokens | 0/5 | 1/5 |
| v4 | 4 | Schema enumerates exact reference identifiers; only r02/r03 repeated | 1/2 | 2/2 |
| New leaves, v3 | 4 | Frozen Luna bitwise and unary candidates | 1/2 | 2/2 |

“Valid report” means the response completed and passed structural/reference
validation. It does not mean the judgment was correct. In particular:

- DeepSeek's v1 r03 report correctly diagnosed the decoder branch, but supplied
  a well-formed instruction as its counterexample. That example does not expose
  the defect. Its v4 report supplied a valid malformed-operand example.
- GLM's v1 selection reports claimed that definitions were elided. The exact
  saved requests contain every line and complete bodies. One affected an
  unchanged control; two missed planted faults. These are unfounded context
  complaints, not evidence that the packet lacked source.
- Several correct diagnoses used prose instead of the exact source-anchor ID.
  They failed validation and remain failed. Enumerating permitted references
  improved the targeted v4 follow-up but was not retested over all five cases.
- DeepSeek's v4 r02 answer described the reversal but omitted a finding and a
  counterexample. That bare rejection was also rejected by the validator.
- There were twelve output-limit failures and one transport timeout in total.
  A timeout does not establish whether the upstream request incurred a charge.

Across all adaptive rounds, DeepSeek supplied two fully supported, validated
seed detections; GLM supplied four. These include repeated cases and are **not**
independent successes or recall estimates. No new defect beyond the seeds was
established. The controls were previously reviewed, not mathematically certified
as faithful to every aspect of the manual.

The two new candidates are pinned separately under [candidates](../../review/candidates).
GLM accepted both; DeepSeek accepted the unary candidate and exhausted its
output allowance on the binary candidate. Their integration relies on
[coordinator source/statement review](../../../docs/formalization/bitwise-leaves-review.md)
and fresh Lean replay, not these model approvals.

## Reproduce without private history

Use a normal clone containing public history, acquire the pinned manual locally,
then run the mechanical cases without paid inference:

```sh
python3 scripts/check_sources.py --fetch
python3 formalization/review/check_cases.py \
  --output .formalization-runs/review-mechanical-fresh
```

[The review guide](../../../docs/formalization/model-review.md) explains new API
invocations. Every request uses a fresh output directory. The source manual,
raw requests, responses and model prose remain local because they may contain
vendor passages. Public hashes identify those artifacts but do not allow a new
reader to inspect an old response without obtaining it separately. Regeneration
can reconstruct inputs, not promise the same output or provider.

Runner v2 is `scripts/model_review.py` at public commit
`7e2af082735e32fa9eae9622503db3e4fc4a992e`. Applying
[runner-v1.patch](../../review/runner-v1.patch) or
[runner-v3.patch](../../review/runner-v3.patch) to that file reconstructs the
respective earlier runner. The current runner is v4. Per-call runner hashes and
settings identify the executed version; v3 additionally pins helper code and
captures the runner bytes when imported, avoiding changes during a batch.
The preserved leaf contracts, all four Luna invocations, evaluator corrections,
selected patches and fresh replays are in the adjacent
[bitwise](../bitwise32/README.md) and [unary](../unary-bits32/README.md) records.

For the next instruction batch, the usable route is still an advisory model
review followed by coordinator adjudication and independent mechanical replay.
A broader, frozen evaluation should precede any automatic acceptance policy.
