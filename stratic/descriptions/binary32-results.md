# Encoded binary32 results and real-number bounds

Binary32 is the single-precision floating-point format used by PTX `.f32`.
Its 32 bits contain a sign, an exponent controlling scale, and a fraction
controlling significant digits. Those bits also represent positive and negative
zero, infinities, and NaNs: special results meaning “not a number.” Very small
finite values called subnormal numbers remain representable with fewer
significant digits. The format adapter preserves every input bit pattern,
including zero signs and NaN payloads, the extra bits distinguishing NaNs.

The adapter uses the pinned FloatLib encoded format already depended on by
TorchLean. Conversion between a PTX word and that format must round-trip exactly.
It does not pass through a host floating-point value, which could change NaN
bits. A finite-value interpretation returns an actual real number only for
finite encodings; exceptional values must not silently become real zero.

A conservative result envelope preserves PTX's freedom in single-precision NaN
results. An envelope contains every result the account must consider; it need
not claim that every included result can occur. When the selected reference
operation returns a NaN, any NaN encoding is included. Otherwise the output must have exactly the reference bits, retaining
signed zero and infinity. The reference result itself always witnesses a
result in this envelope. This does not impose FloatLib's particular NaN payload
on PTX. The pinned manual does not explicitly distinguish quiet and signaling
NaN outputs while
also referring to IEEE 754, the standard for this floating-point arithmetic.
A signaling NaN is marked to request an invalid-operation signal under that
standard; a quiet NaN is not marked that way. Exact realizability of those NaN encodings
remains unresolved; envelope membership is not a hardware existence theorem.

The first reference arithmetic is addition and multiplication rounded to nearest,
with ties choosing the result whose last significant bit is even. This supplies
the numerical foundation for explicit `add.rn.f32` and `mul.rn.f32` on targets
at least `sm_20`. Subnormal inputs and outputs are retained. Flushing small values to
zero, saturation, other rounding modes, multiply-add fusion and approximate
instructions require their own contracts. These are reference arithmetic and
result rules; a separate instruction layer supplies fetch, operands, predicates
and register updates and connects their outcomes to this arithmetic contract.

When the encoded reference result is finite, every output in the envelope has
the same finite encoding. The adapter connects it to one rounding of the exact real
sum or product and transfers the checked absolute rounding-error bound. The
bound is half the spacing of the applicable representable-number grid. It
continues to make sense for very small values where a uniform relative-error
bound would not. Signed zeros have the same real value but retain distinct bits.

Finiteness of the encoded result is an explicit condition of these numerical
theorems, not a consequence of finite inputs alone: large finite inputs can
overflow to infinity. A consumer must prove its intermediate results finite
from its input domain before using the real bound. TorchLean's rounded-real grid
has no upper exponent limit; the encoded-result condition is what makes that
analysis applicable to actual binary32 in this contract. This slice does not
provide general range analysis, a complete floating-point instruction family,
PyTorch bitwise agreement, or a hardware-conformance proof.
