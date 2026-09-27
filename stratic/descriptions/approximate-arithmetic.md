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

A zero-radius neighborhood means equal real values, not necessarily equal bits:
the two signed zeros have the same real value. Instruction rules must add their
required sign and exceptional-value conditions. Widening an allowed radius can
only add outcomes. Several distinct finite words can satisfy a positive-radius
contract; no deterministic reference is silently substituted for those choices.

These are numerical tools for future instruction contracts. They do not yet
implement ex2, reciprocal, a fetched unary instruction, or an executable softmax.
The PTX source review must still justify the chosen allowance and special cases,
and the instruction proof must connect actual operands and outputs to it.
