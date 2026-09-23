# Finite binary32 results from operand ranges

A finite input is an encoded number that represents a real value rather than
infinity or NaN. Finite inputs alone can still overflow when added or multiplied.
This range adapter prevents that outcome using a bound on the exact real
operation before rounding: the magnitude of the sum or product must not exceed
binary32's largest finite positive value, `(2 - 2^-23) * 2^127`.

The check concerns the input real values and their exact sum or product. It does
not assume that the encoded result is finite or equal to the desired answer.
For nearest-even addition and multiplication with gradual underflow, the bound
proves that the reference result is finite. Every output in the parent's result
envelope then has that same finite encoding, represents the rounded exact real
result, and satisfies the existing absolute rounding-error bound. At least one
such output exists because the encoded reference is a witness.

Magnitude bounds can also discharge the condition without evaluating a sum:
if the operand magnitudes are bounded by A and B, addition uses A+B and
multiplication uses A*B, with nonnegative A and B. These are reusable sufficient
conditions. The adapter does not claim that they describe every finite case;
addition can cancel, and nearest-even rounding can return a finite value for
some exact values just beyond the chosen largest-finite guard.

Subnormal values and signed zeros remain part of the encoded model. No normal
input assumption or uniform relative-error bound is introduced. The consumer
still supplies finite input interpretations and proves the concrete range
condition. Automatic range analysis, whole-program intermediate bounds, other
rounding modes, FTZ, saturation and actual PTX instruction execution remain
separate responsibilities.
