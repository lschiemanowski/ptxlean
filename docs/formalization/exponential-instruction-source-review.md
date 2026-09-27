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
