# Numerical meaning and accuracy

The numerical contracts allow the number formats to be chosen for each
implementation; they do not prescribe one precision policy. That policy states
how values are stored, which formats instruction inputs use, and which format
holds a running sum during accumulation. It also specifies rounding to a
representable value, conversions between formats, operation order, and the
allowed error or range of results for approximate instructions. Every result
allowed by the documented instruction behavior must remain represented.

Implementation correspondence proves that the kernels follow this numerical
policy. Accuracy bounds compare their outputs and backward derivatives with the
ideal real-valued computation. A backward derivative calculation can be expressed
as a vector-Jacobian product (VJP): it takes weights on the outputs and returns
the derivative of their weighted sum with respect to selected inputs or
parameters. Comparisons with PyTorch identify the exact version and configuration.
Equality of the output bit patterns and agreement within a stated error are
different guarantees.

An accuracy guarantee covers every permitted result for all inputs satisfying
its stated conditions. A checkpoint is a saved set of model weights. The ideal
reference interprets each finite stored weight as its exact real-number value.
When differentiating, weights remain variables; the saved values specify where
the derivatives are evaluated. Converting those weights to another number format
introduces a separate error obligation.

Forward and backward error bounds account for saved forward values, backward arithmetic, and permitted approximations.

A bound on forward outputs does not automatically bound their derivatives.
A classical derivative describes the function's local rate of change where that
derivative exists. At points where it does not exist, a chosen derivative
convention needs its own contract. A surrogate gradient is a deliberately
substituted derivative rule; it must not be presented as the classical derivative
of the original function.

Error bounds combine across intermediate tensors, the raw output scores called
logits, a scalar objective called the loss, and its derivatives called gradients.
Gradient guarantees include an absolute-error bound on the size of the difference,
rather than relying only on error relative to a possibly zero reference value.
Each bound specifies the allowed inputs, the norm used to measure error size,
requirements that values be finite, and assumptions about sensitivity to small
changes (conditioning). Dependence on sequence length and other parameters is
explicit. Reports explain whether the bound is useful in magnitude, not merely
valid. A numerical reference calculation is itself approximate and is distinct
from the ideal real-valued target.
