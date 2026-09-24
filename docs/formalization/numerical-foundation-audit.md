# Draft audit: a reusable binary32 numerical foundation

**Status: source audit and options, not an accepted numerical policy or an
implemented PTX floating-point slice.** No instruction implementation, Gemma
precision decision, dependency upgrade or external model call belongs to this
change. The audit was performed on 2026-09-23 against the local pinned sources.
The subsequently implemented narrow adapter is explained in the
[binary32 study](../foundations/binary32.md); the options below record the
prerequisite investigation rather than its current implementation status.

The smallest useful next foundation can reuse FloatLib's encoded binary32
arithmetic and TorchLean's finite-result/error bridges. The new work would be
an explicit PTX result relation, an exact word interface and proofs connecting
that relation to the selected numerical specification. Reimplementing binary32
arithmetic is not justified by the inspected dependencies. Using TorchLean's
rounded-real `FP32` alone would omit essential PTX behavior.

## Exact inspected inputs and limits of this audit

The pinned PTX ISA 9.4 HTML has SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
`python3 scripts/check_sources.py` passed: 3,928,316 bytes and 23 manifest anchors.
The additional floating-point anchors below were read from that exact HTML.

The integration manifest and actual dependency checkout heads agreed:

| Dependency | Resolved commit |
| --- | --- |
| TorchLean | `de3192df4779877ceb65cfe470a4d4ce9d480a5b` |
| FloatLib | `c9a051f08f948ce473036b815b0669fafb61f601` |
| mathlib | `5ed2965256430c3649e86755f9576b54eca72435` |
| Lean | integration pins `leanprover/lean4:v4.34.0` |

The manifest resolves FloatLib's upstream `main` to the exact commit above;
ordinary reuse must retain that resolved pin. These packages are currently
available under `integration/torchlean/.lake/packages/`. They are not dependencies
of the small root library merely because the integration imports it.

The initial probe encountered a missing object file for the finite bridge.
A subsequent independent prerequisite check built the pinned targets
`NN.Floats.IEEEExec.Bridge.Finite` (2,508 build jobs) and `NN.Floats.FP32.Error`
(2,121 jobs), then freshly elaborated two audit drivers. All 26 distinct selected
endpoints depend only on `propext`, `Classical.choice` and `Quot.sound`; no
`sorryAx` or additional unchecked axiom occurs in their dependency reports.
Concrete `ExecFloat.Binary 8 23` bit-roundtrip probes and the configured addition
refinement also check. This verifies the selected existing contracts, not every
declaration in the dependency libraries or a PTX adapter that has yet to be built.

The [numerical audit receipt](../../integration/torchlean/numerical-audit/receipt.json)
records commands, exact endpoint names, dependency pins and hashes. Its
[import closure](../../integration/torchlean/numerical-audit/import-closure.json)
comes from Lean's actual imported-module list: 4,111 source modules, including
451 FloatLib, four TorchLean and 1,777 mathlib modules, plus the Lean toolchain and
support packages. Every source in that closure is hashed. No root `Ptx` module
is imported by these probes, and no root-source verification is implied. The
pinned toolchain and manifests are unchanged. Full logs and both drivers are
preserved in the same audit directory.

## What is already available

All paths in this section are relative to the exact dependency checkouts above.
The corresponding immutable repository link can use the listed commit as its
Git revision; the descriptions here are about those commits, not current `main`.

| Layer | Existing definitions/proofs inspected | Consequence for this project |
| --- | --- | --- |
| mathlib | `Mathlib/Data/Dyadic.lean` supplies a dyadic-to-real interpretation and algebra/order facts; `Mathlib/Algebra/Order/Round.lean` supplies general integer rounding. | Useful arithmetic foundations. The inspected mathlib files are not a ready PTX or encoded binary32 implementation. |
| FloatLib encoded values | `FloatLib/Floats/Formats/BinaryInterchange/Format/Catalog.lean`; `Configured/Value/Core.lean`; `IEEE754/Native.lean`. `ExecFloat.Binary 8 23`, `ofBits32`, `toBits32`, `toBits32_ofBits32`, `ofBits32_toBits32`. | A 32-bit encoding can retain every NaN payload and sign, both zeros, infinities, normal and subnormal values. The existing PTX `Word` uses `BitVec 32`; its adapter to `UInt32` needs explicit round-trip proofs. |
| FloatLib reference arithmetic | `BinaryInterchange/Spec/Dyadic.lean`; `Spec/Division.lean`; `Spec/SquareRoot.lean`; `Arithmetic/Proof.lean`. `Model.Proof.add_eq_spec`, `mul_eq_spec`, `fma_eq_spec`. | Exact finite intermediates followed by format rounding, with explicit exceptional cases. FMA is one rounding, not multiply then add. These are software-model refinements, not GPU correspondence. |
| FloatLib dispatched arithmetic | `FloatLib/Floats/ExecFloat/Proof/Arithmetic.lean`: `add_eq_spec`, `sub_eq_spec`, `mul_eq_spec`, `div_eq_spec`, `sqrt_eq_spec`, `fma_eq_spec`. | Generic operations carry capability/refinement assumptions. Audit the concrete configured binary32 instances, not just the generic theorem names. |
| Explicit modes | `BinaryInterchange/Rounding/Mode.lean`; `Configured/Rounding/Runtime.lean` and `Proof.lean`: `Binary.add/sub/mul/div/fma/sqrt` take `Model.IEEERoundingMode`; `toModel_add` through `toModel_sqrt` preserve that mode. | No host global rounding environment is needed. Map each supported PTX qualifier explicitly; do not treat all conversion modes as legal arithmetic modifiers. |
| Real interpretation | `BinaryInterchange/Model/RealSemantics.lean`: `Model.toReal?` returns no real value for NaN/infinity. Total `Model.toReal` maps those cases to zero. | Prefer the partial interpretation or an explicit finiteness proof. An unguarded error theorem about total `toReal` could accidentally make an infinity look like numerical zero. |
| TorchLean rounded reals | `NN/Floats/FP32/Core.lean`: `fexp32 = fltExp (-149) 24`, `rnd32 = nearestEven`, `FP32 = NF ...`. | Gradual underflow grid with precision 24, but **no upper exponent bound, NaNs, infinities or signed zeros**. `ieeeMaxFinite` is a bridge guard, not a largest element of this type. |
| Finite encoded-to-real bridge | `NN/Floats/IEEEExec/Bridge/Finite.lean`: `toReal_add_eq_fp32Round_of_isFinite`, `toReal_mul_eq_fp32Round_of_isFinite`. | The exact premise is finiteness of the encoded result. It cannot be silently replaced by finiteness of inputs. The conclusion is one rounded exact real operation. |
| Error bounds | `NN/Floats/FP32/Error.lean`: `round_abs_error`, `round_relative_error_of_normal`, `add_abs_error` and related operations. | Half-ULP absolute bounds include the gradual-underflow grid. The relative bound `2^-24` requires the stated nonzero/normal-domain premises. |
| Native/CUDA boundary | `NN/Runtime/Autograd/Engine/Cuda/Float32Contract.lean`. | Native result-bit agreement is an explicit runtime/toolchain premise or validation obligation. These contracts do not prove CUDA, cuBLAS or LibTorch implements PTX or the reference library. |

FloatLib also provides explicit status-bearing operations and exact accumulators.
Neither should alter the PTX model by default. A status API is not evidence that
PTX exposes IEEE sticky flags; an exact accumulator rounded once is not the
same algorithm as a sequence or tree of rounded additions.

The TorchLean README describes configured transcendental functions as
deterministic approximations without a universal real-error or correct-rounding
theorem. Its Arb adapter crosses an external enclosure boundary. Neither is an
automatic proof of a PTX approximate instruction contract. This audit found
useful existing components; it did not certify every FloatLib operation or
recover every older TorchLean convenience bridge.

## Pinned PTX requirements the adapter must preserve

The following anchors refer to
[`references/nvidia/ptx-isa-9.4/index.html`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html).
They are source obligations, not implemented coverage claims.

| Source anchor | Rule relevant to a binary32 foundation |
| --- | --- |
| [`floating-point-instructions`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions), §9.7.3 | Single-precision NaN results are unspecified. Instructions with rounding modifiers are IEEE-754 compliant. On `sm_20+`, single-precision subnormal inputs/results are supported by default; `.ftz` flushes them to sign-preserving zero. Legacy target behavior differs. |
| [`rounding-modifiers`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#rounding-modifiers), §6.5.2 | The conversion-level list includes `.rn`, `.rna`, `.rz`, `.rm`, `.rp`, `.rs`, plus integer rounding modifiers. Each instruction has its own subset and version restrictions. Stochastic rounding is not ordinary nearest-even with a different label. |
| [`floating-point-instructions-add`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions-add), §9.7.3.3; corresponding `sub` and `mul` anchors | Scalar arithmetic supports `.rn/.rz/.rm/.rp`. Explicit rounding constrains optimization; omitted rounding defaults to nearest-even but may permit contraction of multiply/add sequences. `.sat` clamps into `[0,1]` and maps NaN to positive zero. |
| [`floating-point-instructions-fma`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions-fma), §9.7.3.6 | Exact product-plus-addend before a single selected rounding; the rounding modifier is required. Scalar `.f32` FMA requires `sm_20+`. |
| [`floating-point-instructions-mad`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions-mad), §9.7.3.7 | Modern `.f32` mad is fused like fma, but legacy targets have materially different behavior. Do not define all mad as multiply then add. |
| [`floating-point-instructions-rcp`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions-rcp), §9.7.3.13 | Approximate reciprocal and correctly rounded reciprocal are different forms. The approximate form has a one-ULP bound and a separate table for zeros, infinities and NaN. |
| [`floating-point-instructions-ex2`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions-ex2), §9.7.3.21 | Approximate base-two exponentiation permits up to two ULP from the correctly rounded result, with separate exceptional-input behavior and FTZ qualifications. A single deterministic exp implementation does not describe all permitted PTX results. |
| [`floating-point-comparisons`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-comparisons), §9.3.1.2 | Ordered/unordered comparisons distinguish NaN behavior; ordinary real comparison cannot stand in for the complete instruction. |
| [`floating-point-instructions-testp`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-instructions-testp), §9.7.3.1 | PTX treats both zeros as normal for this instruction's classification. Do not copy a library's similarly named classifier without checking this convention. |

Further conversion and literal support requires the exact
[`data-movement-and-conversion-instructions-cvt`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#data-movement-and-conversion-instructions-cvt)
and [`floating-point-constants`](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#floating-point-constants)
sections. This draft does not audit their entire format/modifier matrix.

## Concrete options

**Option A: encoded binary32 plus a narrow PTX relation and finite-real bridge.**
Reuse `ExecFloat.Binary 8 23` or its underlying descriptor model, preserving raw
bits at register and memory boundaries. Define an explicit PTX allowed-result
relation rather than making library equality the general instruction contract.
For an initial `add.rn.f32` / `mul.rn.f32` slice on the project's modern target,
non-NaN library results can provide the deterministic case; NaN results need the
source-permitted freedom instead of a fixed library payload/sign. Confirm the
precise NaN classification policy before completing that adapter. Use explicit
rounding, no saturation and no FTZ initially, with unsupported forms rejected
as unsupported. Those restrictions simplify the first slice without removing
subnormals, overflow or infinities from the encoded carrier.

The required reusable foundation is small: bit round trips; classification and
finite interpretation; round-mode mapping; allowed-result membership and
existence; and finite-result transfer to existing real rounding/error theorems.
Instruction fetch/operands, register updates, guard behavior and decoder coverage
remain later Luna instruction work. A source review of the PTX relation must
precede treating a passing kernel proof as evidence of faithful definitions.

**Option B: rounded-real arithmetic first.** TorchLean's `FP32` makes compositional
real-error arguments easier, and could support a small abstract numerical
example. It would still require a proved encoded bridge before claiming PTX
implementation correctness. A model with an unbounded exponent cannot establish
full binary32 exceptional behavior. This is an analysis layer, not a substitute
for Option A's implementation semantics.

**Option C: implement binary32 rounding from bit fields here.** Mathlib's real,
rational and dyadic support would help, but encoding, normalization, all rounding
cases, overflow, underflow, signed zero and exceptional arithmetic would be new
proof work. The inspected pinned FloatLib already supplies most of that work.
This option is justified only by a concrete audit failure or an unacceptable
dependency constraint, neither established by this draft.

The source inspection favors investigating Option A with narrow imports. This
is a recommendation for scope selection, not a numerical-policy decision.
Keep the dependency-heavy adapter in the integration library if preserving the
root library's small dependency footprint is important; otherwise explicitly
review adding the pinned numeric dependency to the root. Either route must make
the compiled/proved boundary and public interfaces visible.

## Obligations before a useful forward/backward numerical example

1. **Every encoded input category has meaning.** Include normal and subnormal
   finite values, both zero signs, infinities and NaNs. Preserve raw bits where
   observed. A chosen NaN payload may witness an allowed result without becoming
   the only permitted result. Confirm signaling/quiet and payload obligations
   from the relevant PTX clauses rather than inherit FloatLib's preference.
2. **Exceptional arithmetic is separate from real error.** Cover invalid
   combinations and overflow in the total result relation. Prove input/domain
   bounds sufficient for finite intermediate results when transferring to reals;
   do not assume the desired final equality or silently discard infinity through
   total `toReal`. The finite-result premise in the existing add/mul bridge is
   an exact obligation to discharge, not a completed range analysis.
3. **Gradual underflow remains represented.** Binary32 has minimum positive
   subnormal `2^-149` and minimum positive normal `2^-126`. An absolute bound at
   small magnitudes remains meaningful when a uniform relative bound does not.
   FTZ, if added later, needs sign-preserving input and output transformations
   and a separately justified error budget. A library quantization-policy flag
   alone does not prove it matches PTX's instruction-level FTZ rules.
4. **Rounding sites and operation order are fixed.** Spell explicit `.rn` for
   the initial scalar forms. Preserve whether a multiply and add are fused,
   sequentially rounded or arranged in a tree. Reduction order and mixed-precision
   conversions belong to the implementation interface, not an algebraic rewrite.
5. **Approximate instructions use relations.** State their documented domain,
   special-value table, reference value and exact ULP definition. Establish
   nonempty permitted results. Prove errors for every permitted observation;
   do not identify the instruction with one library approximation or import an
   unchecked enclosure as a theorem. These obligations can be deferred by an
   initial example using only correctly rounded scalar arithmetic.
6. **Backward correctness has the agreed mathematical target.** Differentiate
   the ideal real-valued cache-free forward specification, use its VJP interface,
   and separately relate a supplied numerical backward program to it. The
   derivative of a discontinuously rounded computation is not the intended
   substitute. TorchLean's automatic mathematical backward construction and a
   manually supplied PTX backward remain separate implementations and proofs.
7. **Torch/PyTorch correspondence is an additional contract.** Precision,
   upload/conversion, operator order, contraction, backend/library versions and
   nondeterministic reductions may differ. A finite-real error result alone is
   neither bitwise PyTorch equivalence nor evidence about a compiled GPU run.

A small supplied scalar affine forward with a separately supplied VJP is a
possible first consumer after scope selection: it exercises products, sums and
rounding without forcing approximate transcendental instructions or a Gemma
policy. Its input/range conditions must prove intermediate finiteness and its
error statement must account for each rounding. This draft does not choose the
example, its constants or its final theorem statement.

## Proposed verification gate for the selected foundation

Build only the chosen pinned imports first, then inspect axiom dependencies of
concrete binary32 round trips, mode/refinement bridges and real-error endpoints.
Prove encoded edge cases with kernel-checked computation where practical: both
zeros, ties on even/odd mantissas, smallest subnormal, normal/subnormal transition,
largest finite value, overflow and invalid-operation NaNs. Test distinguishing
examples for fused versus separate arithmetic and qualifier rejection when those
instruction slices arrive. Such examples complement universal contracts; they
do not establish NVIDIA or hardware conformance.

The audit leaves the following exact decisions open: integration versus root
dependency placement; carrier-level adapter shape; the first supported instruction
forms; NaN relation details; and the first numerical example/range theorem.
No numerical Stratic realization status was changed by this draft.
