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

The initial reciprocal path uses nearest-even division of the encoded value one
by the actual encoded operand. This selects the explicitly rounded PTX form as
the future instruction target and avoids assigning the approximate reciprocal
an undocumented reference convention. A nonzero finite operand and a bound on
the exact quotient establish finite output and the rounded-real meaning of
every permitted result. The NaN envelope preserves the existing uncertainty
about permitted NaN payloads. This is a numerical provider; fetched reciprocal
instructions and their target checks remain separate work.

These are numerical tools for future instruction contracts. They do not yet
implement PTX ex2, a fetched unary instruction, or an executable softmax.
The PTX source review must still justify the chosen allowance and special cases,
and the instruction proof must connect actual operands and outputs to it.
