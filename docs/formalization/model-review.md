# Independent model review

The [Stratic description](../../stratic/descriptions/model-review.md) states the
review contract. `scripts/model_review.py` sends a frozen packet to one explicitly
selected OpenRouter model. It does not run Lean, modify a candidate or accept a
patch. The initial reviewers are `deepseek/deepseek-v4.1-flash` and
`z-ai/glm-5.3-flash`; the observed catalog is preserved under `formalization/review/`.

Acquire the pinned source with `python3 scripts/check_sources.py --fetch`. Put an
OpenRouter key in the ignored `.env` file as `OPENROUTER_API_KEY=...`, or export
that variable in your shell. The optional file reader parses only this variable;
it does not execute the file or expand shell substitutions.

```sh
python3 scripts/model_review.py formalization/review/cases/r01.json \
  --model deepseek/deepseek-v4.1-flash --env-file .env \
  --output .formalization-runs/reviews/r01-deepseek-001
```

Use a fresh output directory for every invocation. A successful request saves its
raw request, response, parsed report and receipt locally. A failed or interrupted
invocation remains recorded; there is no automatic retry. The output-token and
transport-time limits are explicit invocation settings, not semantic verdicts.
The provider may vary; requested and returned identity, provider, timing, usage
and reported cost are preserved where available. Missing cost is not zero.

A recipe names an exact public Git base, hash-pinned candidate/support files,
source sections and authored obligations. An optional saved patch is checked in
a temporary Git index; it cannot alter supporting files. The packet contains the
resulting candidate, not the patch filename or evaluation labels. Each reviewer
gets the same packet in a fresh request with no generating-model conversation.
This first route is a fixed-context review without tools, not an autonomous
repository audit. Structured JSON and valid source references make findings
inspectable; they do not establish their truth.

The pilot cases use two unchanged controls and three faults. Their labels live in
`formalization/review/cases/labels.json` and are never included in requests. This
is an adaptive development set, not held-out evidence of general reviewer
accuracy. Reproduce its mechanical controls without any inference:

```sh
python3 formalization/review/check_cases.py \
  --output .formalization-runs/review-mechanical-fresh
```

Each candidate must compile with its proofs and pass the named dependency audit.
A seeded fault must then fail the distinguishing assertion because it is false;
a build failure or broken evaluator is not counted as detection. The coordinator
adjudicates actual model findings against these obligations and records false
alarms, missed defects, uncertain answers and failures separately. Final
instruction acceptance still requires independent Lean replay and source review.

Raw requests and responses may contain NVIDIA passages and remain local. Public
results contain hashes and project-authored adjudications, not uninspected model
prose. Reconstructing an exact request requires the locally acquired manual;
regeneration does not promise the same model output.

The request format follows OpenRouter's [chat API](https://openrouter.ai/docs/api/api-reference/chat/create-a-chat-completion)
and [structured-output documentation](https://openrouter.ai/docs/guides/features/structured-outputs).
Supported parameters are required when routing; output is also validated locally.

The [first development trial](../../formalization/results/reviewer-pilot/README.md)
retains all 38 invocations and their adjudications, including failed requests and
counterexamples that did not demonstrate the claimed defect. The current request
uses medium reasoning and 16,384 output tokens, with exact obligation IDs,
candidate paths and source anchors enumerated in the response schema. The same
schema appears in the prompt, and local validation remains mandatory. This
improves report formatting; it does not establish semantic accuracy. The pilot
supports using these reviewers as additional evidence, with coordinator review
still required for integration.
