# A ReLU neuron

This scalar example computes F(x,w,b) = max(w*x+b,0): one input, a trainable
weight and bias, and a rectified linear unit (ReLU), which replaces negative
values with zero. The incoming derivative d tells the backward how the final
loss changes with F. Put g = d when w*x+b is positive and g = 0 otherwise;
the returned sensitivities are dx = g*w, dw = g*x and db = g.

TorchLean constructs the real-valued backward from its own multiplication,
addition and ReLU nodes. The generated computation uses zero at the ReLU kink.
That convention defines a backward result at zero, but does not make ReLU
mathematically differentiable there. The ordinary derivative theorem requires
w*x+b to be nonzero. Successful construction and this analytic claim are distinct.

The separately authored PTX computation rounds multiplication and addition
separately in binary32, the usual 32-bit floating-point format. A finite-value
ReLU gate uses existing unsigned comparisons and predicated moves on the stored
bits, avoiding a new unreviewed floating-point instruction. The forward computes
and stores the affine value, then gates it. The cache-free backward recomputes
the affine value, gates the incoming derivative, then multiplies it by the weight
and input in separate launches. Initialized, aligned storage and completed,
visible writes between launches are explicit execution conditions.

Forward error is bounded relative to the ideal real neuron even near zero.
Backward accuracy must account for rounding changing the activation decision:
where the affine error is smaller than the distance of the ideal affine value
from zero, both decisions agree. Outside that region the backward convention
still executes, but agreement with the real derivative is not silently assumed.
Finite inputs, overflow conditions and input encoding errors remain explicit.
Execution existence and memory safety concern the bounded sequential model;
they do not establish a real GPU launch contract or bitwise PyTorch equivalence.
