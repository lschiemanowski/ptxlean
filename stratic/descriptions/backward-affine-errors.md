# Errors in a separately specified squared-affine backward

For the real scalar network `(x*weight+bias)^2`, an incoming output weight d
requests sensitivities of the input, weight and bias. Write A=x*weight+bias.
The exact target values are `2*d*A*weight`, `2*d*A*x` and `2*d*A`. TorchLean's
actual automatically generated backward is proved to have these values. A
separate implementation must still establish its own numerical correspondence.

The numerical contract follows four explicitly selected rounded affine stages:
q=2*d+0, db=q*savedA+0, dx=db*weight+0 and dw=db*x+0. Each stage multiplies and
rounds before adding positive zero and rounding again. The saved forward word
is shared by the two input/weight sensitivities through the actual bias-gradient
word db. No ideal derivative is substituted for a machine intermediate.

Finite interpretations of the initial encoded x, weight, savedA and d are
supplied together with absolute errors relative to their ideal values. The
saved-value error is a separate premise: a forward-kernel theorem can supply it.
The backward theorem does not establish that an arbitrary supplied word came
from a forward execution. Its stage range guards are expressions calculated
from the initial finite values using the explicitly specified rounding order;
no guard assumes an intermediate or gradient output is finite or correct.

For finite actual stage operands lh and rh, the range guards are
`|lh*rh| ≤ M` and `|lh*rh|+eps32(lh*rh) ≤ M`, where M is the largest finite
binary32 magnitude and eps32 is the established absolute rounding allowance.
Write Q=round(round(2*dh)+0) and G=round(round(Q*ah)+0), where dh and ah are
the initial finite seed and saved-value interpretations. The guards are checked
for operand pairs (2,dh), (Q,ah), (G,wh) and (G,xh). Here wh and xh are the
initial finite weight and input interpretations, and round means nearest-even
binary32 rounding. Thus all four pairs are determined before any execution
result is chosen.

Each multiplication's error combines its own rounding with both incoming errors,
including their product. Every explicit zero addition retains its rounding
contribution. The q bound feeds the db bound; that bound feeds both dx and dw.
The result applies to all outputs permitted by the original encoded arithmetic
relations. Existence of those relations is proved separately for arbitrary bits,
without any finite-range hypothesis.

These are scalar arithmetic guarantees for the stated nearest-even binary32
sequence with gradual underflow. They are not a backward code generator or a
PTX execution proof. Separately selected kernels must establish that their actual
stored words follow this sequence; the TorchLean observation interface must
connect the three ideal targets to its actual generated backward. Different
operation orders or formats require their own bounds, and no general network
accuracy tolerance is selected here.
