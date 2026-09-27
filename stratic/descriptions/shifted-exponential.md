# One shifted exponential

This component computes an approximation to exp(x-m) for one finite stored score
x and a supplied finite upper bound m. A later row-maximum computation must
establish that its output is such an upper bound. Here x and m mean the exact
real values of the input binary32 words, not unrounded external data.

The program uses four already modeled instructions: multiply m by exact minus
one, add that result to x, multiply the shifted result by the encoded approximation
to 1/log(2), then apply ex2.approx.f32. Multiplication by minus one is proved to
negate the finite real value exactly. The addition therefore supplies the rounded
subtraction. This representation reuses the existing addition and multiplication
contracts; it does not claim to formalize sub.rn.f32 or improve performance.

The input conditions are x<=m and abs(x),abs(m)<=2^124. These conservative bounds
prevent overflow in the negation, addition and base conversion. The proof derives
that the rounded difference is finite and nonpositive and hence reaches the
supported exponential domain. Finiteness or successful intermediate computations
are conclusions, not extra premises. Both signs of zero and gradual underflow
remain covered by the existing arithmetic contracts.

Write z=round32(x-m), where round32 rounds to the nearest binary32 grid value,
choosing the value with an even final bit on a tie. The shift error is at most
eps32(x-m), the half-ULP rounding allowance. Every permitted final output is finite
and differs from exp(x-m) by at most
`5*2^-24 + log(2)*ExpArgument.budget(z,eps32(x-m))`.
The total bound includes addition rounding, approximation of 1/log(2), multiplication
rounding and the exponential allowance. When x=m, the final word is exactly positive one, including differently signed
zero inputs. The exponential preserves both named ULP
spacing interpretations; no unique hardware result is selected.

The instruction sequence uses one destination register as scratch throughout.
It must differ from the score register, which remains live until the addition.
The destination may coincide with the maximum register because the maximum is
read before that register is overwritten. The standalone sequence starts at instruction position zero. Actual instruction
fetch, original-state
operand reads and four steps connect the final destination to the numerical
bound. An execution exists for every admitted initial state on the selected PTX 9.4
target with SM version at least 20, preserving subnormals without flush-to-zero.
Other word registers, predicates, address registers and memory are preserved.

This is a four-step scalar computation. It neither computes a row maximum nor
proves a parallel launch, memory accesses, a complete softmax kernel or hardware
progress. Finite input values outside the conservative bounds, NaN/infinite
scores, masked rows and input-quantization error need separate treatment.
