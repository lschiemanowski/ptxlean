# A vector-input ReLU neuron

The neuron takes an input vector x, a trainable weight vector w of the same
length, and a scalar bias b. It returns max(sum_i w_i*x_i+b,0). An empty vector
has an empty sum of zero, so the output is ReLU(b). TorchLean builds the actual
graph from its multiplication, sum, addition and ReLU nodes and constructs its
backward automatically. Given an incoming loss sensitivity d, the backward
returns dx_i=g*w_i, dw_i=g*x_i and db=g, where g=d for a positive affine value
and g=0 otherwise. The zero result at the kink is a convention. Ordinary
mathematical differentiation requires the affine value to be nonzero.

The separately authored PTX computation first runs the sequential binary32 dot
product, then computes the bias step and applies the finite-value ReLU gate.
The bias step reuses the scalar affine kernel: multiply the dot result by one,
then add the bias. Those are actual separately rounded instructions. The
cache-free backward recomputes the dot product and affine value, gates d, then
runs the scalar affine kernel twice per coordinate to compute g*w_i+0 and g*x_i+0.
The one and positive-zero constants are initialized storage values. This uses
three forward launches and 3+2*n backward launches, including for empty vectors.
It favors reuse and a transparent correctness argument over launch efficiency.

One allocation holds scalar scratch, constants, bias and incoming sensitivity,
then contiguous weight, input, input-gradient and weight-gradient arrays. The
arrays have equal length and distinct storage. The kernel sequence preserves the
inputs, parameters, constants, incoming sensitivity and trailing storage. Launch
arguments and the dot-product count are supplied explicitly; other registers can
start arbitrarily. Each launch contains an actual instruction run and publishes
its writes before the next launch, without interference. Existence and memory
safety are proved in this bounded sequential model, not assumed from the desired
numeric result. Actual instruction result choices remain represented.

Numerical conditions refer to finite encoded inputs, their deviations from ideal
real inputs, and explicit rounded expressions in those initial values. The dot
product contributes its accumulated error; the bias step contributes its input
and rounding errors. ReLU cannot enlarge the forward absolute error. Backward
agreement requires that affine error budget to be smaller than the magnitude of
the ideal affine value, which proves that rounding cannot change the activation
branch. Gradient multiplication/addition ranges and incoming sensitivity error
are explicit. The resulting stored gradients approximate the actual generated
TorchLean backward, with ordinary derivative meaning on this same domain.

The component covers lengths n below 2^32, binary32 arithmetic, and one thread
per launch. That length bound also rules out 64-bit address wrap for this layout,
including the loop's one-past pointers. It does not supply a CUDA launch
wrapper, a concurrent reduction, mixed precision, a fused operation, bitwise
PyTorch equality or hardware conformance. Checking the Lean proofs remains
separate from assessing fidelity of the reused instruction semantics.
