# Numerical meaning and accuracy

Numerical contracts are precision-parametric. Concrete implementations specify
storage and operand formats, accumulation, rounding, conversions, operation
order, and approximate-instruction behavior. Contracts preserve the documented
set of permitted results.

Implementation correspondence establishes that kernels obey their numerical
policy. Accuracy bounds relate their outputs and VJPs to the ideal real-valued
computation under explicit premises. Correspondence with a concrete, versioned
PyTorch implementation identifies the relevant configuration and distinguishes
bitwise equality from bounded numerical agreement.

Accuracy guarantees cover every permitted result within the stated domain.
The real-valued checkpoint reference uses the exact real values represented by
its stored finite weights. Parameters remain variables when differentiated;
checkpoint values specify an evaluation point. Subsequent precision conversions
introduce separate error obligations.

Forward and backward error bounds account for saved forward values, backward arithmetic, and permitted approximations.

A forward error bound alone does not justify differentiating an approximation.
Classical derivatives, conventions at nondifferentiable points, and surrogate
gradients have distinct contracts.

Composable bounds cover intermediate tensors, logits, loss, and gradients.
Gradient guarantees include an absolute-error component. Bounds expose their
domains, norms, finiteness and conditioning premises, and dependence on sequence
length or other parameters. Reports explain the magnitude and practical meaning
of the resulting bounds; validity alone does not establish useful accuracy.
Numerical reference computations are distinguished from real-valued ground
truth.
