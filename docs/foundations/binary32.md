# From 32 bits to a numerical guarantee

A PTX register containing `0x3f800000` can be interpreted as the binary32 number
one. The register itself still holds 32 bits. Keeping that distinction lets us
state both exact output-bit contracts and numerical error bounds without
confusing them.

The adapter lives in the [pinned integration package](../../integration/torchlean/README.md).
It reuses FloatLib's checked software encoding and arithmetic and TorchLean's
rounding-error theorems. It does not use host floating-point arithmetic as a
proof oracle. The core PTX library remains independent of these larger numerical
dependencies.

## Three boundaries

[The adapter](../../integration/torchlean/PtxBinary32.lean) has three layers:

1. `decode` and `encode` connect a `BitVec 32` word to FloatLib's encoded
   binary32 carrier. Both directions round-trip exactly, for every pattern.
   In particular, they preserve the sign of zero and the bits distinguishing
   different NaNs.
2. `Envelope` describes candidate output bits relative to a reference result.
   A non-NaN result requires exact bits. A NaN result admits every NaN encoding.
   This last rule is a conservative envelope; the project does not claim that
   every admitted signaling NaN can occur under PTX or on hardware. The reference
   result witnesses nonemptiness of the envelope.
3. `finiteReal` returns `some r` for a finite encoding and `none` for infinities
   and NaNs. Error theorems use this guarded interpretation. They never turn an
   exceptional value into a real zero to obtain a numerical equality.

The current `reference` selects nearest-even addition or multiplication from
FloatLib. Nearest-even chooses the closest representable value, breaking exact
halfway ties in favor of an even last bit of the significant digits, called
the significand. Subnormal inputs and
results remain present. The intended PTX forms spell the rounding explicitly:
`add.rn.f32` and `mul.rn.f32`, on targets at least `sm_20`. Other rounding,
saturation, flush-to-zero, approximate operations and fusion are separate
obligations. No instruction fetch or register-update semantics is delivered by
this numerical adapter alone.

## Reading the error theorem

Suppose `left` and `right` are words and we have proved
`finiteReal left = some x` and `finiteReal right = some y`. For addition the
exact real target is `x + y`; for multiplication it is `x * y`.

`results_abs_error` also requires the *encoded reference result* to be finite.
For every candidate output in the envelope, it then produces a real output `z`
and proves that the absolute difference between `z` and the exact target is at
most `eps32` of that target. This is the half-spacing bound supplied by the
pinned gradual-underflow rounding grid. The theorem covers every output in the
envelope, not just the reference chosen to witness existence.

Why require finite results separately? Two finite inputs can overflow. The
[boundary examples](../../integration/torchlean/PtxBinary32Examples.lean) check
that adding the largest finite binary32 word to itself produces positive
infinity. The theorem must not pretend that this result lies on a finite real
number line. The [range adapter](binary32-ranges.md) supplies sufficient input conditions for avoiding
such overflow; its conditions remain visible rather than being replaced by an
assumption of the expected output.

TorchLean's analysis grid has gradual underflow but no upper exponent limit.
The finite encoded bridge is therefore essential. A theorem about that grid
alone would not establish binary32 overflow behavior. Absolute error also remains
useful near zero, where a uniform relative-error claim would fail.

## Concrete encoded checks

All of these are Lean-kernel checked propositions about the selected reference:

| Example | Encoded result or distinction |
| --- | --- |
| One plus one | `0x40000000`, the value two |
| One plus exactly half its next spacing | Rounds down to `0x3f800000`, whose last bit is even |
| The next word above one plus the same half-spacing | Rounds up to `0x3f800002`, whose last bit is even |
| The smallest positive subnormal plus itself | Word `2`; it is not flushed to zero |
| Negative zero times one | Negative zero, `0x80000000` |
| Largest finite value plus itself | Positive infinity; finiteness does not follow from finite operands |
| Positive infinity plus negative infinity | A NaN reference; different NaN payloads belong to the envelope |

The examples complement the universal bit-roundtrip and error theorems. They
are neither hardware experiments nor a proof of complete PTX floating-point
coverage. The [source review](binary32-source-review.md) records the NaN
qualification and target rules; the [independent proof review](binary32-proof-review.md)
records exactly which local declarations were rebuilt and audited.

The [error-composition guide](binary32-error-composition.md) carries input errors
through addition, multiplication, and a multiply followed by a separate addition.
Its second-stage overflow condition depends on the inputs and the first rounding
allowance; it does not assume an accurate intermediate answer.
