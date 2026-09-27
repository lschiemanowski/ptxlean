# Independent normalization review

Reviewer: the sum execution/proof agent, who did not author the normalization modules.

Result: no blocker found in the reviewed component contracts. The review covers
mathematical and implementation correspondence within the existing instruction
semantics; it does not independently establish NVIDIA hardware conformance.

## Reviewed content

- `integration/torchlean/PtxBinary32/Normalize.lean`: `7b8536c8a18a81d3cc55266045a648bc3dea989033c64ea84ffe39d0f1df3740`
- `integration/torchlean/PtxBinary32/SoftmaxNormalize.lean`: `4929eb7fd20f4035552bbcb86044f8d8277663b688a0657d93b4e6bc673ea7df`
- `integration/torchlean/PtxBinary32/NormalizeProgram.lean`: `13dd1908be723f5fc586142e3ae32f96b414b7764829c1719b19972ed370b234`
- `stratic/descriptions/softmax-sum-normalization.md`: `d6727725773d9c2819fe12f1ab60770581420f39b07fa2a9e1490dd7f755067f`

- `integration/torchlean/PtxBinary32/NormalizeCorrect.lean`: `cbde756af586591296106b01990e5ccf8035d9c26034a210465c92958506c10f`

## Findings

`Normalize.Stages` retains an actual encoded reciprocal intermediate, and its
multiplication consumes that same word. The real-value theorem derives the
reciprocal range from the finite denominator being at least one half, then
derives product finiteness from the numerator magnitude bound. It does not
assume the result is finite. Numerators may be negative. Both nearest-even
rounding errors remain explicit, so the sequence is not described as a single
correctly rounded division.

`SoftmaxNormalize` derives the denominator lower bound from the ideal sum's
lower bound, exponential errors and a separate sum error. The total error guard
of one half is visible in the theorem. The proof derives the numerator bound;
it does not silently assume approximate exponentials are nonnegative. The
coordinate theorem concerns supplied encoded arithmetic stages, and does not
claim a combined parallel softmax launch.

`NormalizeProgram` requires two actual fetched instructions and derives both
arithmetic relations, final PC and register/memory/address/predicate frames.
The first write may overwrite the denominator because its original value has
already been consumed; it must not overwrite the live numerator. This exact
restriction is checked by the proof. Execution existence constructs both encoded
intermediates using the existing leaf result-existence theorems. Its target
condition agrees with both represented leaves (pinned ISA 9.4 and SM >= 2.0).

The Stratic prose distinguishes this scalar normalization sequence from the
parallel sum and explicitly leaves combined storage/execution unfinished. Its
allocation, signed-input and error-budget descriptions agree with the modules.
The final prose was rechecked after adding the shifted-exponential range and
register-interface links: the magnitude bound refers to actual encoded outputs;
the register handoff uses the actual stored sum and explicitly leaves PTX loads,
broadcast and combined execution unfinished. This final prose check does not
constitute an independent review of the connector authored by this reviewer.

## Verification

Fresh direct elaboration commands, from `integration/torchlean`:

```
lake env lean PtxBinary32/Normalize.lean
lake env lean PtxBinary32/SoftmaxNormalize.lean
lake env lean PtxBinary32/NormalizeProgram.lean
lake env lean PtxBinary32/NormalizeCorrect.lean
```

Dependency inspection used `#print axioms` for all twelve public proof declarations
in those four modules: `reciprocal_bounds`, `product_range`, `correct`,
`stages_exist`, `numerator_bound`, `denominator_lower`, `encoded_stages`,
`coordinate_accuracy`, `run_results`, `execution_exists`, scalar `correct` and
`finite_execution_exists`. Each reported only
`propext`, `Classical.choice` and `Quot.sound`.
