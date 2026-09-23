# Independent proof review of encoded binary32 results

The reviewed core has no blocking proof issue. This review checks the Lean
statements and their dependencies. The separate
[source review](binary32-source-review.md) evaluates the PTX interpretation and
records the unresolved quiet/signaling NaN-output question. Successful checking
of this foundation does not establish a fetched PTX instruction, GPU execution,
or an exact characterization of every permitted PTX NaN bit pattern.

## Exact representation and finite interpretation

`Value` is the actual pinned `ExecFloat.Binary 8 23`. `decode` and `encode` use
its `UInt32` interchange interface and PTX's `BitVec 32` word. The two universal
roundtrip theorems preserve every bit, not merely the value of finite numbers.
Thus zero signs and NaN payloads cannot disappear through a real-number
conversion or a host floating-point literal.

`finiteReal` first checks the encoded finiteness classifier. It returns `none`
for every non-finite encoding and the actual model real value only in the finite
branch. Its `isSome` theorem exactly matches that classifier. The use of
FloatLib's total `Model.toReal` inside this guarded branch therefore does not
silently reinterpret NaN or infinity as zero. The helper `exact` also uses total
real projections, but its advertised numerical use retains guards, as discussed
below; it is not an unconditional interpretation of exceptional operands.

## Result envelope and existence

`Envelope reference output` admits any NaN output if the reference is NaN.
Otherwise it requires bitwise equality with the reference. This keeps signed
zeros and infinities distinct. It does not replace all non-finite results by a
single exceptional value. `envelope_self`, `envelope_exists`, and `results_exists`
construct the reference as a member, for every input word and operation.

This is nonemptiness of a mathematical result envelope. It is not instruction
termination, device existence, or realizability of every included NaN word.
A relation deliberately larger than the actual output set can support sound
universal finite conclusions; its exact source correspondence remains a separate
obligation. The source review explains why the all-NaN choice is explicitly
conservative instead of inheriting FloatLib's particular payload selection.

## Real rounding and error transfer

`reference` invokes the pinned configured addition or multiplication; this enum
is not a decoder. `reference_round` uses the actual upstream nearest-even
finite-result bridge. Its premise is finiteness of the **encoded reference
result**, not just finiteness of the inputs. The upstream add/multiply theorem
also establishes finite operands from that result premise, so no exceptional
operand is being silently assigned zero in the proof of this rounding identity.

`results_round` is quantified over every output satisfying `Results`.
`envelope_finite_eq` derives equality with the finite reference, rather than
assuming the desired output. It follows that `finiteReal output` is the rounded
exact real sum or product.

`results_abs_error` additionally takes explicit hypotheses
`finiteReal left = some x` and `finiteReal right = some y`. These identify the
actual operand values. It constructs the rounded result as a real witness and
transfers TorchLean's absolute rounding bound to it. The theorem retains the
encoded-result finiteness condition. It neither proves a sufficient input range
nor replaces the conditional contract by an assumed numerical answer.

The target real rounding grid has gradual underflow but no upper exponent limit;
this is why encoded result finiteness matters. The absolute bound remains valid
near subnormal values. No unconditional relative-error bound, FTZ behavior,
other rounding direction, fused operation, approximate instruction or PyTorch
correspondence is proved here. Real interpretation merges zero signs, while
the encoded result relation retains them.

## Checked snapshot

The core target built successfully with 2,515 build jobs. An independent import
driver audited all 16 public core theorems and these nine definitions: `decode`,
`encode`, `isNaN`, `isFinite`, `finiteReal`, `Envelope`, `reference`, `Results`,
and `exact`. Every report contains only `propext`, `Classical.choice` and
`Quot.sound`; no omitted proof or new unchecked axiom appears in those transitive
dependencies. These are proof-visible library semantics, not a certification of
native compiler/runtime replacements.

Reviewed `integration/torchlean/PtxBinary32.lean` SHA-256:
`652adf5073b937101b6f1f187719fd14dd9208f1105d39d0e72743916ecd5e13`.

The dependency pins and earlier finite-format/real-error prerequisite checks are
recorded in the [numerical audit receipt](../../integration/torchlean/numerical-audit/receipt.json).
The separate `PtxBinary32Examples` target built successfully (2,516 jobs),
fresh source elaboration passed, and every one of its 16 named theorems was
independently audited with only the same standard axioms. All computational
proofs use kernel-checked `decide`; there is no `native_decide` step.

The examples cover distinct zero signs and finite zero classification, smallest
and boundary subnormals, ordinary addition, ties at even and odd significands,
gradual-underflow addition, signed-zero multiplication/addition, finite-input
overflow, invalid infinite sums/products, and rejection of exceptional values
by `finiteReal`. Distinct NaN payloads are both admitted. The signaling-NaN
example expressly asserts only envelope membership, preserving the source
review's unresolved realizability boundary. These examples supplement the
universal contracts; they are not hardware measurements or exhaustive semantic
validation.

Reviewed `integration/torchlean/PtxBinary32Examples.lean` SHA-256:
`f0c7b01e37c224376c81c5c2677b528fe4ae484b28c9ba89e7968324b220d116`.

## Input-only sufficient bounds

The independently reviewed `PtxBinary32Bounds` module closes the conditional
finiteness obligation for a conservative input range. `finiteReal_spec` extracts
both operand finiteness and the actual real value; its hypothesis cannot be
satisfied by assigning a convenient real value to an exceptional encoding.
`reference_finite` applies the pinned FloatLib finite-operation theorems to the
exact input sum or product bounded in absolute value by binary32's maximum finite
number, `(2 - 2⁻²³) × 2¹²⁷`. The multiplication proof correctly converts the
absolute product into the product of absolute values.

`round_of_range` and `results_error` quantify over every admitted result. They
derive the core's finite-reference premise from those input conditions and then
reuse the exact rounded-real identity and absolute error bound. Neither includes
an output-finiteness or desired-output premise. `finite_result_exists` uses the
already established reference witness and adds finiteness and accuracy; it still
does not assert an instruction execution exists.

The magnitude helpers use the triangle and product inequalities, and the product
helper derives the required nonnegativity of its bound rather than omitting it.
Unit-bounded values give an elementary nonempty range. The `+1` and `-1` examples
identify actual encodings and discharge the range condition for both operations.
The sufficient bound is conservative: exact results just beyond maximum finite
can still round to a finite value, and that larger region is not claimed here.
No relative-error claim is added, so zero and subnormal results remain within the
stated absolute-error contract.

Reviewed `integration/torchlean/PtxBinary32Bounds.lean` SHA-256:
`9e35494b173c88806d3e8beaa33527121a3ecd93e1102408a8df07575031eb27`.

The reproducible `integration/torchlean/check.sh` default build and fresh aggregate
audit passed, including all 12 public bounds theorems. Their dependencies contain
only the same three standard axioms. This completes review of 44 public binary32
theorems and the nine core adapter/reference definitions; the aggregate checker
also audits the existing graph and tensor bridge endpoints. The exact lists are
in `PtxIntegrationAudit.lean`; the later composition extension is reviewed below.


## Incoming error and sequential composition

The independently reviewed `PtxBinary32Error` module separates a finite encoded
operand's actual real value from the ideal value it approximates. The deviation
hypotheses are input contracts. They imply the error budgets are nonnegative;
no unstated sign condition is needed. Addition uses the triangle inequality.
Multiplication expands both perturbations and retains the cross term `ex * ey`,
so the estimate does not assume second-order error vanishes.

`add_results` and `mul_results` first derive finite encoded output and local
rounding error from the actual input range. They then add the incoming error.
The rounding allowance is evaluated at the actual pre-rounding expression, not
at a conveniently substituted ideal expression. Both theorems remain universal
over the outputs admitted by the encoded result relation. Their existence
corollaries choose actual reference words and do not assume an accurate output.

`AffineResults` joins multiplication and addition by the same intermediate word.
`affine_results` derives that word's real value as the rounded actual product.
The second-stage guard uses only the exact actual product, its proved local
rounding allowance, and the bias magnitude; `rounded_add_range` applies the
triangle inequality to obtain the required addition range. The final bound has
two local rounding terms, the complete product perturbation bound, and the bias
error. Both stage finiteness conclusions are proved. There is no hypothesis
that the intermediate or final word already has the desired accuracy.
`affine_exists` constructs both stages before proving these properties.

The range guards are conservative sufficient conditions, not a complete
characterization of safe cancellation or nonoverflow. These are scalar encoded
relations and exact-real error propagation. They do not prove a fetched PTX
program, an FMA, a tensor operation, a network, or native/device correspondence.
The accompanying [composition guide](binary32-error-composition.md) preserves
these distinctions and the two-rounding operation order.

Reviewed `integration/torchlean/PtxBinary32Error.lean` SHA-256:
`fd2ddedbd7837787fc263694b33de40ee151663c716e9fe18e72369631100ac7`.

The expanded default integration build and fresh aggregate dependency audit
passed all 85 explicitly listed endpoints, including every one of the ten
public composition theorems. Independent fresh source elaboration of the Error
module also passed. All dependencies are confined to `propext`,
`Classical.choice` and `Quot.sound`. The checker verified the actual Lean 4.34
version, all 16 manifest Git revisions and tracked dependency cleanliness,
and unchanged integration/root PTX sources and checker inputs during the run.
This yields 54 reviewed public binary32 theorems plus the nine audited core
adapter/reference definitions. The graph and integer tensor bridge endpoints
account for the remainder of the aggregate audit.
