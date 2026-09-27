# Independent source review: one shifted exponential

Reviewed the proposed sequence against the pinned local PTX ISA 9.4 manual (`.ptx-source/9.4/index.html`, SHA256 `0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`) and current `PtxBinary32.lean`, `PtxBinary32/Instructions.lean`, `PtxBinary32/ExpArgument.lean`, `PtxBinary32/Exponential.lean`, and `PtxBinary32/ExponentialInstruction.lean`. Principal manual anchors: `floating-point-instructions-add`, `floating-point-instructions-mul`, `floating-point-instructions-ex2`. This report paraphrases rather than redistributes the source.

## Finding

The route is semantically defensible within the existing reviewed model:

```
mul.rn.f32 negM, m, 0fbf800000;
add.rn.f32 shifted, x, negM;
mul.rn.f32 argument, shifted, 0f3fb8aa3b;
ex2.approx.f32 out, argument;
```

The exact binary32 literals encode -1 and 12102203/8388608. The latter is an approximation to 1/log(2), not that real constant itself. The real comparison target is exp(x-m), where x and m are the real values of initial finite encoded inputs. This is a four-instruction implementation of the difference; it does not add a formalized `sub.rn.f32` instruction and must not be advertised as doing so.

## Conditions and proof obligations

1. Preserve explicit `.rn` on addition and multiplication and omit `.ftz`. The source gives nearest-even behavior for `.rn`, preserves subnormal inputs/results on SM>=20 without `.ftz`, and warns that unmodified multiply/add sequences may be optimized to fused operations. These exact spellings and the existing PTX=94, SM>=20 model restriction are consequential, not incidental syntax.
2. Negation by multiplication with exactly -1 is exact for finite binary32 values, including subnormals and the largest finite magnitudes. Prove this from representability and the executable arithmetic bridge rather than assuming a zero-error multiplication. The real theorem forgets the sign of zero; do not claim a particular zero encoding without a bit-level proof.
3. A finite pair x<=m does not alone ensure finite subtraction: opposite large magnitudes can overflow. Require an explicit bound on the exact difference, or a transparent sufficient bound on initial magnitudes. Separately ensure the rounded shift multiplied by the encoded conversion constant stays within finite range. Derive intermediate finiteness and ex2 supportedness from those input conditions rather than assuming them as final-state properties.
4. x<=m implies the exact difference is nonpositive. Nearest-even rounding is monotone and fixes zero, so the rounded shift is nonpositive; multiplication by the positive conversion constant followed by the same rounding is likewise nonpositive. No artificial strictly-negative or normal-only restriction is needed. Both zero signs, negative subnormals, and underflow remain in scope.
5. In particular x=m yields a real zero after the shift and conversion and the bounded ex2 provider enforces exact output encoding +1. This exact special case is stronger than the generic approximate envelope and should survive composition. Testing both signs of input zero is useful because real equality alone erases that distinction.
6. The scalar leaves read operands from the pre-state, so source/destination aliases within an instruction are legitimate. Across the sequence, however, the initial x value must survive until the add. A scratch destination distinct from x is a sufficient ordinary condition; it may overwrite m once m has been consumed. Later shifted/argument/out registers may reuse one scratch register if frame reasoning reflects actual dataflow. If the implementation chooses separate fixed registers, document that choice instead of implying arbitrary alias support. All-result proofs must use the operands read by actual fetched instructions, not only an isolated arithmetic relation.
7. The last instruction remains nondeterministic. Relate every admitted output to exp(x-m); do not silently select the reference result or restrict to nonnegative outputs. The current conservative two-policy ex2 envelope can admit tiny negative outputs near underflow. Its source interpretation remains explicitly qualified; source fidelity is not established merely by Lean checking.
8. Execution existence should construct the four fetched steps at the actual start PC and derive the bounded exponential's domain membership. Preserve memory, address registers, predicates and unrelated word registers. This is a finite register-only local sequence, not a parallel maximum reduction, launchable softmax kernel, fairness argument or GPU conformance result.

## Review boundary

No blocking source mismatch was found in the proposed route. This reviews the proposal and existing building blocks, not code that has not yet been written. The finished sequence and numerical theorem still need independent proof review and completed kernel checks. The all-output accuracy statement inherits the explicitly named conservative ULP interpretation and does not establish that every admitted output bit pattern is realized on hardware. Raw PTX parsing and register-declaration/type compatibility remain the existing frontend boundary.

---

# Independent proof review: one shifted exponential

Reviewed `integration/torchlean/PtxBinary32/ShiftedExp.lean` (SHA256 `ee41beeb7e65eac133c0c4f9b34f3cebf682ce069185c007e68a16a0de61a3b9`) and `ShiftedExpProgram.lean` (SHA256 `443d6d2314ad292063f1d744c1ce5a08aa7d1a320da842fb3ea00392912d82cb`) against the Stratic description and `/tmp/shift-source-review.md`, and inspected their arithmetic, instruction, and exponential dependencies. Follow-up review also covers `ShiftedExpChecks.lean` (SHA256 `9b8c44fda9ebc87b7da12a646ab24de38011dfdaf5c7c5292eeafbf54ccf79d4`).

## Result

No blocking proof or semantic-composition issue found in the final versions, including the maximum-score exact-one theorem and behavioral checks.

## Findings

- The only numerical premises are finite initial encoded values, their ordering, and their magnitudes bounded by 2^124. No assumed finite intermediate, supported exponential operand, or successful arithmetic stage conceals a missing operation. `negative_real` establishes representability-preserving negation through the executable arithmetic bridge. `shift_real` obtains subtraction by rounded addition, derives finiteness and nonpositivity, and uses monotonicity plus a representable endpoint to bound the rounded result. The existing conversion theorem then derives the finite nonpositive exponential operand.
- The arithmetic and program correctness theorems cover every permitted exponential result. There is no positivity constraint on the final approximation, no selection of a convenient result, and no bypass of the inherited conservative ULP envelope. The error compares against the real exponential of the exact real interpretations of the stored input words.
- The mixed instruction `Step` requires actual indexing at the current program counter. `run_results` recovers the fetched instructions at PCs 0, 1, 2, and 3 through the preceding frame equations. The destination theorem binds outputs to each actual intermediate state, not to free intermediate witnesses. The mixed target gate is exactly the existing binary leaf gate, definitionally the same as the exponential leaf gate (ISA 94 and SM >=20).
- `destination != input` is sufficient for preserving the live original score until addition. The destination may alias maximum because the first instruction reads it from the pre-state. Input and maximum may also coincide if the destination differs. Each subsequent stage reads the previous scratch result. All unrelated word registers, memory, address registers, and predicates are preserved.
- `execution_exists` first constructs arithmetic witnesses under the input conditions, then explicitly constructs all four successor states and fetched steps. Its existence is separate from the all-execution bound, avoiding a vacuous correctness claim. The program is standalone, starts at PC 0, and ends at PC 4; arbitrary placement or embedding is not proved.
- This introduces no `sub.rn.f32` model. It composes explicit `mul.rn.f32`, `add.rn.f32`, `mul.rn.f32`, and `ex2.approx.f32` leaves. PTX source fidelity, raw parsing/type declarations, full hardware behavior, parallel maximum reduction, and GPU progress remain outside the result.

## Documentation correction (resolved)

The original description said “The budget includes ... and the exponential allowance.” `ExpArgument.budget` contains addition error, conversion-constant error and conversion-multiplication error only. The exponential allowance is the separate `5*2^-24` term. Change this to “The total bound includes ...”, or explain the two terms separately. The description now uses “The total bound includes ...” and explicitly states the standalone PC-0 placement; both review points are resolved.

## Mechanical corroboration

Independently ran `lake env lean /tmp/shift-review-audit.lean` from `integration/torchlean`. This checked a temporary exact copy of the reviewed program module and printed dependencies of `negative_real`, `shift_real`, `error`, `stages_exist`, `run_results`, `correct`, and `execution_exists`. All passed; each reports only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, new axiom, or native unchecked evaluation was found in the two sources. This is corroboration of the manual review, not a replacement for source fidelity review or the project's full combined checks.

## Follow-up: exact maximum and behavioral obligations

`equal_scores` and `maximal_score` derive the intermediate shifted and converted values as real zero from the actual arithmetic relations and then apply the exact zero branch of the exponential relation. Thus the destination is exactly encoded +1 for every run when the score equals the supplied maximum, even with opposite zero signs. This does not impose any additional condition on intermediate encodings. The exact-one guarantee is useful for the later denominator proof, although the reduction and denominator argument are not part of this change.

The checks cover exact instruction spellings, no execution without fetch, no execution on unsupported targets, destination aliasing the maximum, preservation of the smallest negative subnormal during the shift, inclusive opposite-sign 2^124 input endpoints, an actual signed-zero run with exact-one output and preserved score/memory, and a genuinely negative shifted-score execution tied to the general accuracy theorem. Endpoint existence is numerical; signed-zero and negative-score examples instantiate the fetched program. None is represented as a hardware run or a full softmax result.

Independently ran `lake env lean /tmp/shift-review-final-audit.lean`, containing an exact temporary copy of the final checks source plus eleven dependency queries for the two new theorems and all nine checks. It passed. `spellings` has no axioms; all other queried declarations report only `propext`, `Classical.choice`, and `Quot.sound`. The full project checks remain the coordinator's separate responsibility.

## Integration boundary

The implemented component uses existing accepted instruction leaves, so this
change adds no ISA form and makes no Luna or external-model API call. Independent
agents reviewed the source interpretation and completed proofs separately from
the implementation. The combined integration checker builds all three new modules,
freshly checks the boundary examples, and audits all 30 new public declarations.
The project-wide checks and exact reviewed tree are recorded with Stratic.
