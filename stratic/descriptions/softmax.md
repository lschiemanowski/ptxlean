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

The first reciprocal implementation uses explicitly nearest-even rounding, the
PTX spelling rcp.rn.f32. Its encoded numerical provider is division of one by
the actual computed denominator. A sufficient input guard D<=1/2 makes that
denominator at least one half, so its reciprocal is at most two and has a finite
encoded rounded result. This stronger guard establishes representability, which
does not follow merely from positivity. The provider's half-ULP rounding error
discharges the local reciprocal obligation for the actual destination of an
enabled fetched reciprocal instruction. Nonpositive base-two exponentials also have finite encoded
rounded centers and a universal neighborhood error bound. A wider finite relation
covers both center-based and output-based ULP spacing: ULP is the floating-point
grid spacing, which changes with magnitude. Every allowed result has error at
most 5*2^-24, including reference rounding. This covers the two named conventions;
it does not identify a unique interpretation of the PTX source.

Natural exponentials also need conversion to base two. The concrete binary32
constant 0x3fb8aa3b represents c=12102203/8388608, approximating 1/log(2).
For a nonpositive encoded shifted score x approximating ideal score t<=0 with
error h, the actual rounded product x*c has argument error at most
`B = eps32(x*c) + abs(x)*abs(c-1/log(2)) + h/log(2)`.
Here eps32 is the half-ULP rounding error allowance. Every result in the finite
exponential relation on that product has error at most 5*2^-24+log(2)*B from
exp(t). Finiteness follows from an input product bound; abs(x)<=2^126 is a simple
sufficient guard. These base-conversion theorems construct encoded arithmetic witnesses; the
separate instruction leaf below supplies exact special cases and fetched steps.
The shifted-exponential component derives the subtraction error from the original
stored score and a supplied upper bound, then connects all stages to a four-step
instruction sequence.

The first scope is a nonempty unmasked row. Empty rows, masked-out positions and
rows with no enabled positions need explicit separate policies. The reciprocal leaf and the bounded ex2.approx.f32 leaf connect to their
numerical providers. The exponential leaf supports nonpositive finite inputs,
infinities and NaNs; positive finite inputs remain explicitly unsupported, even
when their exponentials would be finite. Signed-zero inputs produce exact
positive one. Its existence theorem requires a disabled predicate or an input
in that supported domain. This is a partial instruction model, not full ex2
coverage. These components do not yet establish that a combined softmax kernel
realizes every stage contract or has a completed execution.
A bounded four-step scalar sequence now implements one shifted exponential and
returns exact positive one when the score equals the supplied maximum. It derives
finite, nonpositive intermediates from its input conditions and preserves every
permitted final result. A parallel maximum component selects an original input
word that bounds every finite score in a power-of-two row of at most 1024 entries.
It proves correctness for every completed admitted execution, a separate completed
execution witness, memory safety and preservation of the input storage.
A parallel sum reduces the encoded exponentials with derived finite-range and
rounding bounds. A two-instruction scalar sequence normalizes each numerator
using the actual stored sum through an explicit register interface. The total
exponential and sum error must be at most one half to derive safe normalization.
The interface does not implement PTX loads or broadcast between these components.
Remaining work includes combined softmax forward and backward programs, with
admitted execution existence, memory safety and stored-output proofs for their
composition.
GPU execution and benchmarking remain deferred.
