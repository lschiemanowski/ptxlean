# Independent source review: encoded binary32 result envelope

This review checks the selected contract in
[`binary32-results`](../../stratic/descriptions/binary32-results.md) against the
pinned PTX ISA 9.4 source and the pinned FloatLib/TorchLean definitions. It
reviews the numerical foundation, not an implemented `add`/`mul` instruction
frontend, a GPU, or a Gemma precision policy.

**Conclusion:** the encoded carrier, nearest-even addition/multiplication,
gradual-underflow interpretation and conditional finite-real transfer are
appropriate for the narrow scope. One qualification is necessary: admitting
**every** NaN encoding should be documented as a conservative result envelope,
not an exact characterization of which NaN words PTX or hardware can produce.
The quiet/signaling distinction is not resolved by the inspected PTX wording.
Do not silently narrow the relation to FloatLib's selected quiet NaN encoding.

## Reviewed sources

The normative PTX input is
[`references/nvidia/ptx-isa-9.4/index.html`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html),
SHA-256 `0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
Relevant sections were read from that exact file:

- [§5.2.1, fundamental types](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#fundamental-types):
  the same-size bit type is compatible with the corresponding fundamental type.
- [§9.7.3, floating-point instructions](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions):
  IEEE compliance, subnormal treatment, single-precision NaN freedom and saturation.
- [§9.7.3.3, floating-point add](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions-add):
  exact syntax, rounding options, optimization/contraction qualification, target
  conditions, FTZ and saturation.
- [§9.7.3.5, floating-point mul](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions-mul):
  the corresponding scalar multiplication clauses.

The dependency versions are FloatLib
`c9a051f08f948ce473036b815b0669fafb61f601`, TorchLean
`de3192df4779877ceb65cfe470a4d4ce9d480a5b`, mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, and Lean 4.34.0.
The separate [prerequisite audit](../formalization/numerical-foundation-audit.md)
and its receipt report the targeted builds and theorem-dependency checks.
Those checks establish proof validity for the library statements; this source
review evaluates the intended PTX correspondence separately.

## NaN freedom: preserve the uncertainty explicitly

Two statements occur together in §9.7.3:

> Instructions that support rounding modifiers are IEEE-754 compliant.

> Single-precision instructions return an unspecified NaN.

The surrounding text says double-precision payloads are supported and warns
programs against relying on the particular single-precision NaN generated.
A search of the pinned HTML found no floating-point quiet/signaling-NaN
classification rule settling the output quiet bit. The occurrences of
“signaling” concern barriers, not floating-point encodings. This absence is
not proof that every signaling NaN can actually be produced: the inherited
IEEE-compliance clause must also be respected.

FloatLib's NaN selection is concrete: signaling operands are considered before
ordinary NaNs, then the selected NaN is quieted; payload/sign selection follows
its explicit reference definitions. These choices are useful for an executable
witness. They must not become a claim that PTX promises the same payload, sign
or operand-priority rule.

The proposed relation admits any encoded NaN when the reference is NaN, and
otherwise requires exact reference bits. On NaN results this is a conservative
over-approximation of the permitted-result set. A theorem quantified over all
members remains safe if the true PTX set is narrower: proving a property for
more outputs does not lose an actual output. In the finite-result theorems the
NaN branch is excluded altogether, so this ambiguity cannot weaken their
finite numerical conclusion.

Three claims must remain distinct:

1. The envelope is nonempty because the reference is a member.
2. A property is proved for every result in that envelope.
3. Every admitted bit pattern can occur in PTX or hardware.

The first two are suitable statements for this foundation. The third is not
established by this review, particularly for signaling NaN output encodings.
Reference membership alone is not an instruction-execution or hardware-existence
proof either. Exact NaN-set characterization can be investigated later without
changing current finite-result theorems.

Recommended wording for the contract is “a conservative envelope preserving
PTX's unspecified NaN freedom,” with an explicit note that the possible
quiet/signaling subset is not characterized. This records the unresolved source
question instead of quietly choosing a narrower output set.

## Finite arithmetic, signed zero and exceptional results

The scalar forms reviewed here are explicitly `add.rn.f32` and `mul.rn.f32`,
without `.ftz` or `.sat`. Their selected rounding mode is nearest with ties to
even. The reference should use the library's proved nearest-even operation,
not a host `Float` computation or decimal conversion. A PTX word-to-encoded-value
adapter must preserve all 32 bits and prove both round trips.

Signed zeros are different encodings even though both map to real zero.
Requiring exact non-NaN reference bits preserves the distinction in operation
results. FloatLib's inspected dyadic addition path preserves negative zero when
both zero operands are negative and uses positive zero for opposite-sign exact
cancellation under nearest-even. Its multiplication reference uses sign XOR,
including zero products. These are the relevant reference rules; projecting to
reals alone would fail to expose a wrong zero sign.

Infinities remain encoded results and are not excluded by the total envelope.
Invalid operations can produce NaN through the reference branch. Finite inputs
alone do not establish finite results: addition and multiplication may overflow.
The numerical bridge's premise is explicitly finiteness of the **encoded
reference result**. Under that premise the envelope forces exact output equality
and hence the output is finite as well.

TorchLean's `FP32` rounded-real grid has no upper exponent bound. The pinned
`toReal_add_eq_fp32Round_of_isFinite` and
`toReal_mul_eq_fp32Round_of_isFinite` bridges provide the necessary conditional
connection to encoded arithmetic. Their half-grid-spacing absolute bound can
then be transferred to every admitted finite output. This neither proves an
input range sufficient for finiteness nor supplies general overflow analysis.
Those obligations belong to each later program's domain proof.

FloatLib's total `Model.toReal` maps NaN and infinity to zero. Consequently a
public finite interpretation should expose `toReal?`, an equivalent relation,
or a finiteness premise, as the selected description requires. The use of the
total projection inside an already-guarded theorem is not an error; losing the
guard or presenting it as an unconditional physical value would be.

## Subnormal and target boundary

A subnormal is a very small finite value with fewer significant digits. The
selected carrier and nearest-even operation retain subnormal inputs and results.
PTX documents this default for scalar single precision on `sm_20` and later.
The same omission of `.ftz` on legacy `sm_1x` does not have that meaning.
Therefore the adapter's intended PTX reading must state a target at least
`sm_20`; the project's existing `sm_70+` slice is sufficient. “Modern target”
alone should not be the final machine-readable applicability condition.

Scalar add/mul originated in PTX 1.0, and their `.rn` modifier is available on
all targets. The stronger target condition here comes from preserving
subnormals, not from first availability of nearest-even addition/multiplication.
The review is pinned to ISA 9.4; it does not claim coverage of packed `.f32x2`
forms or their newer target requirements.

Gradual-underflow real rounding uses precision 24 and minimum subnormal scale
`2^-149`. An absolute error bound remains meaningful near zero. A uniform
relative bound such as `2^-24` requires its own nonzero/normal hypotheses and
is not part of the unqualified absolute result. FTZ would require separately
modeling sign-preserving input and result flushing. Saturation would require
clamping and the stated NaN-to-positive-zero behavior. Neither is covered by
the present envelope over the unmodified reference operation.

## Explicit rounding and the later instruction connection

The add/mul clauses distinguish an explicit rounding qualifier from its omission.
Although omission defaults numerically to nearest-even for the individual
operation, a multiply/add sequence without explicit rounding can be contracted
by optimization. The selected contract's reference arithmetic is therefore
appropriate for the explicitly qualified forms, not a proof that every bare
`mul.f32; add.f32` pair performs two independent roundings.

The future frontend must fetch the actual supported instruction, read its actual
operands, retain its explicit qualifier and target conditions, and emit/register
an output satisfying the relation. It must reject unsupported qualifier
combinations as unsupported rather than quietly ignore them. Predicate-false
execution, bit-preserving moves, memory representation and arithmetic results
are separate cases. This foundation does not prove any of those instruction
connections merely by defining a result envelope.

Approximate instructions and fused multiply-add are outside this selected slice.
Their result sets and rounding sites require separate source contracts. No
inference about Torch/PyTorch backend ordering, native library correctness or
Gemma precision follows from the encoded scalar foundation.

## Review disposition

Proceed with the narrow foundation if its description records the conservative
NaN-envelope qualification and an explicit modern-target threshold. There is no
identified blocker for exact word preservation, reference nonemptiness, or the
finite-reference transfer/error statements. Keep the quiet/signaling output-set
question visible as a limit on exact source characterization. This document
adds no implementation axiom and does not change the allowed-output definition.
