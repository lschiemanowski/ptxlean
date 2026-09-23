# Finite results from input ranges

The encoded binary32 foundation has an important condition on its real-number
error theorems: the reference result must be finite. Two finite inputs can still
overflow. `PtxBinary32Bounds` replaces that result condition with a sufficient
condition about the input values and their exact mathematical operation.

Suppose words `a` and `b` have finite real interpretations x and y. The new
`reference_finite` theorem proves the encoded nearest-even reference result is
finite whenever:

- for addition, `|x + y| ≤ M`;
- for multiplication, `|x * y| ≤ M`;

where `M = (2 - 2^-23) * 2^127`, the largest finite positive binary32 value.
`maxFinite_eq` checks this formula against FloatLib's actual encoded-format
maximum. The bound is on exact real arithmetic before rounding. No hypothesis
assumes the encoded result is already finite or equals a proposed answer.

The underlying pinned FloatLib lemmas are
`Model.isFinite_add_of_abs_toReal_add_le_posMaxFinite` and
`Model.isFinite_mul_of_abs_mul_le_posMaxFinite`. The multiplication lemma uses
`|x| * |y|`; the adapter uses the exact identity `|x*y| = |x|*|y|`. Both require
finite inputs and an IEEE format. The binary32 specialization supplies those
facts from the partial finite interpretations and the pinned format descriptor.

Once finiteness follows, `round_of_range` proves that every admitted result has
the real value obtained by rounding the exact sum or product once to nearest,
with ties to even. `results_error` gives the existing half-grid-spacing absolute
error bound and finite output classification. `finite_result_exists` produces
an admitted finite encoded output with that same bound. The witness is software
reference arithmetic; this is not a proof of a fetched PTX instruction or GPU
execution.

The range check is deliberately sufficient rather than necessary. Cancellation
can make addition safe even when operand magnitudes are large. Also, some exact
values just beyond M can round back to a finite result. Those cases need other
proofs if a consumer wants to admit them; this adapter does not redefine them
as invalid PTX behavior.

## Simple magnitude certificates

Bounds on each operand compose without requiring an exact symbolic sum:

- `add_range_of_magnitudes` uses `|x| ≤ A`, `|y| ≤ B` and `A+B ≤ M`;
- `mul_range_of_magnitudes` uses the same operand bounds and `A*B ≤ M`.

The magnitude bounds themselves imply nonnegative A and B. `unit_range` shows
that `|x| ≤ 1` and `|y| ≤ 1` suffice for either operation: a sum has magnitude at
most two, and a product at most one. These bounds do not restrict the inputs to
normal numbers, and so include subnormals and both zero signs.

For a concrete encoded example, `positive_one_real` interprets word `0x3f800000`
as +1, and `negative_one_real` interprets `0xbf800000` as -1. Their input bounds
establish `one_negative_one_results` for both operations without a result-finite
premise. The exact real sum is zero and the exact real product is -1. This
example demonstrates use of the range interface; the theorem states the general
rounded-value/error contract rather than relying on these particular operations
being exactly representable.

The [source review](binary32-source-review.md) remains the scope boundary:
explicit `.rn` arithmetic, gradual underflow on `sm_20+` (including the project's
`sm_70+` slice), no FTZ or saturation, and a conservative NaN envelope. Finite
input/range premises exclude the NaN branch for these results without narrowing
the parent relation. No uniform relative-error theorem, automatic whole-program
range analysis, mixed-precision policy or Torch/PyTorch bitwise agreement follows
from this adapter.
