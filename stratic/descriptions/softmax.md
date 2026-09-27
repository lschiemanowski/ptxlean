# Stable softmax

Softmax turns a nonempty row of real scores into positive weights that sum to
one. The stable formula subtracts the row's largest score before taking
exponentials, then divides each exponential by their sum. Subtracting the same
value from every score leaves the exact real result unchanged. At least one
shifted score is zero, so one exponential is one; all others lie between zero
and one. The exact denominator therefore lies between one and the row length.

The reference is the pinned TorchLean stable softmax specification. Its existing
analysis establishes these bounds and proves that its backward rule is the
true vector-Jacobian product: for output weights p and incoming sensitivities d,
the input sensitivity is p_i*(d_i-sum_j p_j*d_j). An incoming sensitivity says
how strongly each output contributes to the surrounding computation's result.
This smooth function does not need ReLU's away-from-zero activation condition.
A backward kernel will be supplied separately from TorchLean's automatic reverse
construction.

Numerical composition keeps four errors separate. Each computed exponential has
an absolute error delta_i, including any error in preparing its argument. The
computed sum has error sigma relative to the sum of those computed values. The
reciprocal has error rho relative to one divided by that computed sum. The final
multiplication has error tau_i relative to its actual operands. These are local
component obligations, not an assumed final softmax error.

Let D=sigma+sum_i delta_i. If D<1, the computed denominator is at least 1-D and
is strictly positive. Every collection of stage values satisfying those local
bounds has coordinate error at most
`tau_i + (1+delta_i)*rho + (delta_i+D)/(1-D)`
against TorchLean's real softmax. This bound allows approximate exponentials to
round to zero. It does not promise positive computed outputs or an exactly
unit computed sum. The sum's departure from one is bounded by the sum of the
coordinate error bounds. The row length enters through the accumulated errors.
The D<1 condition is a sufficient condition for this bound, not a claim that
softmax fails whenever the bound cannot establish it.

For backward arithmetic, a dot-product error budget combines errors in the
forward weights and incoming sensitivities with the dot product's own rounding
error. The final coordinate bound also includes subtraction and multiplication
errors. Write epsilon_i for the forward-weight error, eta_i for the incoming
sensitivity error, and sigmaDot for the computed dot product's error relative
to its actual operands. Then
`Q = sigmaDot + sum_i (abs(d_i)*epsilon_i + abs(pHat_i)*eta_i)`
bounds the dot-product error against `q=sum_i p_i*d_i`. With local subtraction
and multiplication errors subError_i and mulError_i, the backward coordinate
error is at most
`mulError_i + abs(d_i-q)*epsilon_i + abs(pHat_i)*(subError_i+eta_i+Q)`.
The composed theorem uses the computed forward outputs as pHat and derives
epsilon from the forward theorem. A forward error guarantee alone is not a
backward correctness theorem.

The first scope is a nonempty unmasked row. Empty rows, masked-out positions and
rows with no enabled positions need explicit separate policies. This numerical
foundation does not yet claim that PTX instructions realize the stage contracts,
that stage values are realizable binary32 words, or that a kernel executes.
Remaining work is the source-reviewed approximate arithmetic, a parallel maximum
and sum implementation with rounding/range bounds, fetched forward and backward
programs, admitted execution existence, memory safety and stored-output proofs.
GPU execution and benchmarking remain deferred.
