# Scalar PCG instruction contracts

The scalar solver entries run one thread. They compute norms, choose the two
PCG coefficients, and update status flags. This review covers the additional
instruction forms needed for those entries. It is a manual comparison with
NVIDIA's specification; Lean checks the consequences of the definitions.
Neither activity proves GPU conformance.

The source is the locally pinned PTX ISA 9.4 document, SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The document is not redistributed. The relevant sections are §9.7.3.9 (abs),
§9.7.3.12 (max), §9.7.3.15 (sqrt), §9.7.7.2 (setp), §9.7.9.1 (and),
and §9.7.9.4 (not), together with the existing move, selection, predication,
load/store and unsigned address-arithmetic contracts.

The additional contracts are deliberately narrow:

- `sqrt.rn.f64` uses the pinned Lean binary64 square-root model with rounding
  to nearest, ties to even. Negative numerical inputs produce NaN, while either
  zero keeps its sign. NaN result encodings remain unconstrained after decoding.
  No approximate square root or flush-to-zero mode is included.
- `abs.f64` clears the sign bit for numerical values, including subnormal
  values and negative zero. The pinned text specifically retains a NaN input's
  bits. The definition therefore returns that original word; replacing it by
  an unconditional sign-bit mask would miss this detail. NVIDIA discusses a
  possible future change, which is not silently substituted for the pinned rule.
- Unmodified `max.f64` returns the numerical operand when only one input is
  NaN. When both are NaN, the result is a NaN with unconstrained encoding.
  Positive zero ranks above negative zero. Ordinary numeric comparison alone
  is insufficient to implement this zero tie.
- The used `setp.gt.f64` and `setp.le.f64` comparisons are ordered: either NaN
  input makes the predicate false. Unsigned equality examines the low 32 bits.
- Predicate conjunction and negation inspect actual predicate registers.
  Conditional division executes its arithmetic only when the stored predicate
  has the requested value. Otherwise it advances without changing the
  destination. The coefficient or branch outcome is never a proof premise.
- `selp.u32` chooses an actual operand using the predicate. A conditional
  `mov.u32` changes the destination only when enabled. The model's wider register
  container stores the resulting 32-bit word with zero high bits.
- Four-byte status stores use the actual computed address and low 32 operand
  bits. They require four-byte alignment and an in-allocation, nonwrapping
  access, and write exactly four little-endian bytes. The scalar address
  calculation includes the emitted immediate-zero widening multiply; it is
  not replaced by a register-zero assumption.

The used binary64 forms are permitted on the selected `sm_120` target. In
particular, binary64 abs/max and round-to-nearest square root require at least
`sm_13`; the emitted PTX version explicitly spells the square-root rounding.
No architecture-wide support claim follows from these small contracts.

`ScalarExtras` wraps the existing scalar instruction semantics and adds these
forms without changing the earlier concurrent proofs. `ScalarExtrasChecks`
contains kernel-checked examples for both zero signs, a NaN payload, subnormal
absolute value, ordered NaN comparisons and square root. These examples can
catch definition mistakes; they do not replace the source review or prove the
external native implementation used by compiled Lean code.
