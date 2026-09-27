# Bounded exponential instruction: source and acceptance boundary

The reviewed source is the locally acquired PTX ISA 9.4 manual with SHA256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The principal section is `floating-point-instructions-ex2`; related anchors are
`predicated-execution`, `instruction-statements`, `source-operands`,
`destination-operands`, `operand-type-information`, `fundamental-types` and
`floating-point-constants`. This document is our paraphrase, not bundled vendor
text. A separate semantic reviewer verified the source and the following scope.

## Deliberately partial input coverage

The selected spelling is `ex2.approx.f32` without `.ftz`. The project uses exactly
PTX 9.4 and an SM >=20 feature floor for preserved subnormals. These are project
restrictions, not the instruction's minimum version: the operation predates the
explicit `.approx` modifier, which appeared in PTX 1.4.

The provider supports finite nonpositive operands, both infinities and NaNs.
Signed zeros give exactly positive one. Negative infinity gives positive zero;
positive infinity gives positive infinity. A NaN input permits any NaN output
in the project's conservative payload policy. This does not claim hardware
realizability of every payload.

Strictly negative finite input uses the proved union of two named two-ULP
policies: spacing measured at the nearest-even rounded reference, or at the
returned value. The source does not identify this ULP evaluation point in the
reviewed instruction section. The union is a declared conservative interpretation
over those policies, not evidence that the manual uniquely means either one.
Neither output positivity nor a neighboring-encoding convention is silently
added. The numerical proofs cover every admitted output, including gradual
underflow and tiny negative results in the model's error neighborhood.

Positive finite operands remain unsupported, including ordinary inputs that
would not overflow. They are legal PTX inputs. Absence of an enabled step in this
fragment is missing model coverage, not NVIDIA undefined behavior. Consequently
an existence theorem must expose supported-input membership or a disabled guard.
A false predicate skips even an unsupported operand without evaluating arithmetic.

## Worker and coverage boundary

The worker supplies a typed unary leaf with real fetch, source/destination
aliasing, both predicate polarities, precise occurrence records and frame proofs.
It reuses the coordinator's numerical provider. It does not choose one allowed
approximate result or assume unconditional arithmetic existence.

The complete acceptance driver must pass against a separate coordinator reference
fixture and reject independently compiling semantic mutants before dispatch.
The fixture is excluded from the worker's inputs. The frozen driver also checks
exact zero/special cases, generic allowed-output inclusion, positive-input
rejection, disabled positive-input skipping, actual nonzero fetch and all-result
finite accuracy. Fresh replay and independent candidate review are required before
integration. Worker process completion alone is not acceptance.

This fragment remains outside the accepted-form ledger and its full-form counts.
The HTML catalog's existing restricted-model category can show it with its input
and interpretation limits. Raw PTX parsing, register declaration validation,
positive finite/overflow behavior, other forms, parallel softmax execution and
hardware conformance remain separate work.

## Completed pre-dispatch calibration

The complete frozen driver passed against a separate coordinator-authored
reference fixture. Four altered fixtures compiled and passed their own public
axiom audits, but failed the independent driver: ignored input operand, FTZ
spelling, fetch fixed to position zero, and weakened SM floor. The reference
fixture and calibration logs are retained as coordinator effort, separately from
the worker candidate. The fixture is not part of the worker task base or inputs.

A draft driver was repaired before dispatch: an explicitly typed constructor
application replaced a slow implicit-instruction inference in the test for both
predicate polarities. A stale overflow-coverage comment was also corrected.
The final full-driver calibration used the corrected exact bytes; none of this
is a post-generation checker change. Earlier diagnostics are retained as draft
checker-development records, not acceptance evidence. These mutations exercise
particular errors; they do not prove the checker detects every possible defect.

## Candidate acceptance

The headless runner made two calls requesting GPT-6 Luna (campaign calls 33 and
34). The first candidate left the typed decoder proof incomplete. A targeted
repair changed only that proof body; instruction definitions, theorem statements,
provider and frozen acceptance driver were unchanged. The coordinator did not
edit the candidate. Provider-confirmed model identity was not reported.

The semantic reviewer inspected initial candidate SHA256
`146f6dfbc0de8a82efcaf0d763293c740fc74ea30afb98cd94b3fcfe6b301258`.
A separate proof reviewer inspected the final candidate SHA256
`2b5f1a0d063d0aa5349c32b6c40da81fc7f192b2bd8fa5b6c28596f7d9b4b5f7`,
confirmed the proof-only difference, and found no remaining issue in the bounded
contract. Fresh replay checked the final candidate, frozen driver and all 24
public declarations; dependencies are limited to Lean's standard `propext`,
`Classical.choice` and `Quot.sound`.

The first replay exhausted `/tmp` file entries while unpacking dependencies and
could not save its final status. Its logs and recovery note are retained. Only
task-owned generated dependency caches were removed, then a new replay on the
main filesystem passed. This resource failure is not omitted or counted as a
successful proof check. The [trial record](../../formalization/results/exponential-instruction-v1/README.md)
includes both attempts, both replays and pre-dispatch calibration evidence.
