# Composing binary32 arithmetic errors

An encoded operand can already differ from the ideal real value it approximates:
for example, it may have been rounded by an earlier operation. Error composition
accounts for both those incoming errors and the next operation's rounding.
It applies to every output in the binary32 result envelope, not just one chosen
reference calculation.

Suppose the actual finite input values are xh and yh, while the ideal values are
x and y. Bounds ex and ey satisfy `|xh-x| ≤ ex` and `|yh-y| ≤ ey`. Addition
introduces at most its own absolute rounding bound plus ex+ey. Multiplication
introduces at most its own rounding bound plus `|x|*ey + |y|*ex + ex*ey`.
The product term accounts for both inputs being perturbed simultaneously; it is
not discarded as negligible. The deviation premises already imply nonnegative
error bounds.

Each encoded operation must pass the existing input-range guard on its actual
finite operands. The guard proves finite output before the absolute-error
bridge is used. Every admitted output then satisfies the composed error bound,
and an admitted finite output exists. The numerical proof does not assume the
output is close to the ideal value as a premise.

A two-stage affine expression first multiplies and rounds, then adds a finite
bias and rounds again. Its bound includes both rounding contributions, the two
multiplicand input errors and the bias input error. The second stage's range
can be established conservatively from the exact product magnitude, its local
rounding bound and the actual bias magnitude. The intermediate word is an actual
output of the first result relation and an actual input of the second. This
operation order is distinct from a fused multiply-add, which rounds only once.

These are scalar numerical composition rules for nearest-even binary32 with
gradual underflow. They are not floating-point instruction execution, a complete
neural-network error analysis, a GPU correctness claim, or a selected Gemma
precision policy. Larger programs must supply their own finite input/range and
incoming-error proofs and preserve their actual operation order.
