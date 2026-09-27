# Approximate arithmetic bounds

An approximate instruction may return several different bit patterns for the
same inputs. Its accuracy contract must cover every permitted result. A finite
error neighborhood contains binary32 words whose real values lie within a stated
absolute distance of a finite center word. An exceptional value, such as infinity
or NaN (not a number), does not belong to this finite neighborhood. Exceptional
instruction behavior therefore needs a separate contract.

The distance can be expressed in units in the last place, abbreviated ULP. This
is the spacing of the binary32 grid at a chosen real value, with a smallest step
of 2^-149 near zero. The chosen convention uses the pinned FloatLib/TorchLean ULP
at the center. At a power-of-two boundary, the spacing changes, so this convention
is explicit. A numerical neighborhood is not a claim that NVIDIA uses exactly
this convention, nor that every included bit pattern is physically realizable.

A nonnegative-radius neighborhood always contains its finite center. Membership
provides an actual finite real value and an absolute distance bound. If the
center is itself within error E of the ideal result, all members are within the
neighborhood radius plus E. In particular, a correctly rounded real center
contributes its rounding error in addition to the approximation allowance.
Theorems must not discard that extra rounding term.

A finite center can be constructed from any real input whose absolute value is
at most binary32's largest finite value. Round that input to the nearest grid
point, resolving exact halfway cases toward the value with an even final binary
digit, and encode the resulting integer times a power of two. Monotonicity of
rounding proves that this grid point is still within the finite range. The
encoding theorem returns an actual word and proves that its finite real value
is the rounded input; it does not assume output finiteness or representability.
This is a mathematical, non-executable construction for relational semantics,
not a software implementation of an exponential.

For nonpositive arguments, a base-two exponential lies between zero and one;
for arguments at least one, a reciprocal lies between zero and one. These input
domains therefore admit finite rounded centers, including gradual underflow to
zero. They are useful sufficient domains for stable softmax, not the full PTX
instruction domains. The approximate-result relation still permits every word
in its stated neighborhood rather than replacing that relation by its center.
For an ideal value between zero and one, both it and its rounded center have
ULP at most 2^-23. A count-k neighborhood therefore has total absolute error at
most (k+1/2)*2^-23. For the two-ULP exponential allowance this is 5*2^-24.
This conservative estimate includes rounding and does not assert that an
instruction attains every included value.

A zero-radius neighborhood means equal real values, not necessarily equal bits:
the two signed zeros have the same real value. Instruction rules must add their
required sign and exceptional-value conditions. Widening an allowed radius can
only add outcomes. Several distinct finite words can satisfy a positive-radius
contract; no deterministic reference is silently substituted for those choices.

The reciprocal provider uses nearest-even division of the encoded value one by
the actual encoded operand. The fetched rcp.rn.f32 instruction preserves exactly
this result relation and checks the selected PTX version and target. A nonzero
finite operand and a bound on the exact quotient establish finite output and
the rounded-real meaning of every permitted result. These are numerical-analysis
conditions, not restrictions on instruction execution. The NaN envelope preserves
the existing uncertainty about permitted NaN payloads. Approximate reciprocal
and its error convention remain separate work.

The exponential relations are numerical tools for future instruction contracts.
They do not yet implement PTX ex2 or an executable softmax.
The PTX source review must still justify the chosen allowance and special cases,
and the instruction proof must connect actual operands and outputs to it.

Measuring ULP at the output can permit a value excluded by measuring it at the
center. A checked boundary example uses center 1/2-2^-25 and output 1/2+2^-24:
their distance is three center steps but only one and a half output steps.
Thus the center convention cannot be called a conservative replacement for the
output convention. This example distinguishes numerical policies; it does not
claim that a GPU produces that output or that this center is reached by an
encoded exponential operand. A source-faithful exponential contract still needs
an explicit interpretation policy and separate exceptional-value cases.

A second neighborhood deliberately covers both choices of where to measure ULP:
at the finite center and at the finite returned value. It uses the larger of
these two spacings. Every result admitted by either choice belongs to this
neighborhood, and the center itself is an encoded witness that it is nonempty.
This covers these two named interpretations only; it does not establish that
NVIDIA uniquely specifies either one or cover an unproved interpretation based
on counting adjacent encodings.

For a center between zero and one, a two-ULP result in this wider neighborhood
still has distance at most 2*2^-23 from the center. This bound is derived without
assuming that the returned value lies between zero and one: a global bound on
spacing first constrains its magnitude, and then the local spacing bound applies.
Adding nearest-even rounding error gives absolute error at most 5*2^-24 from an
ideal value between zero and one. Hence the same numerical error budget can be
used for a nonpositive base-two exponential under either named interpretation.
The relation retains signed zeros and possible tiny negative results; special
instruction cases and any source-mandated sign conditions remain separate.

Converting a natural exponential to base two uses a concrete binary32 constant,
0x3fb8aa3b, approximating 1/log(2), and an ordinary rounded multiplication by
that constant. Its error budget keeps three contributions visible: any error
already present in the shifted input, the constant's error, and multiplication
rounding. For nonpositive inputs, rounding preserves the nonpositive sign;
the exponential sensitivity bound then carries argument error to output error.
A finite multiplication result requires a bound on the exact product before
rounding. The resulting theorem applies to actual encoded multiplication and
approximate outputs, but does not claim that a fetched kernel has performed the
shift, multiplication, or exponential. It leaves the constant's error as an
explicit real expression, not an unverified decimal estimate.

The bounded exponential provider separates exact special cases from its finite
approximation neighborhood. Signed-zero inputs return positive one exactly;
infinities and NaN follow their documented cases. A strictly negative finite
operand preserves every result in the two-policy neighborhood. Positive finite
operands are explicitly unsupported by this initial fragment. Result existence
is equivalent to the stated supported domain, so missing overflow semantics
cannot disappear behind an unconditional existence assumption.
