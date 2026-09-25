# The generated affine-square backward result

The scalar example computes `(x*w+b)^2`, where x is the input, w is a variable
weight and b is a variable bias. Scalar here means a tensor containing one
number, with no dimensions. The forward graph is the existing TorchLean graph;
this component does not replace it with a separately invented computation.

The seed is the derivative arriving from the rest of a computation. If this
network's output F feeds a final loss L, the caller supplies d = ∂L/∂F. The
backward then returns the derivatives of L with respect to x, w and b by the
chain rule. To obtain the gradient of F itself, the caller supplies d = 1.
The seed is an input to the backward, not another parameter of the forward.

For any real x, w, b and seed d, TorchLean's checked backward call succeeds and
returns the three input sensitivities in order: `2*d*(x*w+b)*w` for x,
`2*d*(x*w+b)*x` for w, and `2*d*(x*w+b)` for b. Its returned forward value is
`(x*w+b)^2`. This general interface is a vector–Jacobian product: it propagates
supplied output sensitivities back to the inputs, including when a network has
several outputs.

These formulas are conclusions about the actual automatically generated
backward computation. Neither the desired gradient nor successful execution
is assumed. The square node uses the same input twice, so reverse accumulation
must include both contributions. The generated result also retains the existing
proof that it is the adjoint derivative of the actual graph's forward map.

All values and derivatives here are exact real numbers. This does not supply
a PTX backward program, prove termination of a PTX kernel, differentiate floating
rounding, or bound floating-point gradient error. A PTX backward implementation
and its correspondence proof remain separate work. Weight and bias are both
differentiable inputs; they are not fixed external graph data.
