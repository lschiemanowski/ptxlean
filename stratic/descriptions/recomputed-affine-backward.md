# A separately authored squared-affine backward implementation

This example verifies a particular PTX implementation of the backward for the
real scalar network `(x*weight+bias)^2`. The output weight d selects the desired
weighted derivative. TorchLean constructs the reference backward automatically;
the PTX request sequence is selected separately and its correspondence is proved
from its actual instruction executions.

The implementation first recomputes A=x*weight+bias, with separate binary32
multiplication and addition. It then computes q=2*d+0, db=q*A+0, dx=db*weight+0
and dw=db*x+0 using four more affine-kernel launches. The initial bias word can
be reused for the saved A word because its load precedes the first store. The
final three gradient words represent input, weight and bias sensitivities, in
that order. Each addition of zero remains an actual rounded instruction.
This is a simple recomputing backward implementation, not an optimized kernel
or a complete forward invocation returning the squared output.

The ten initial words are input, weight, bias, incoming output weight, positive
two, positive zero, arbitrary old input/weight/bias-gradient bits, and arbitrary
old q bits. Extra words remain unchanged. All five launches use one live
device-owned allocation and each has independently supplied initial registers.
A valid completed chain must follow the five actual instruction traces and write
exactly the characterized intermediate and gradient words. Such a chain exists
for arbitrary encoded initial inputs under the target and storage conditions.

The numerical guarantee starts with finite interpretations and representation
errors for input, weight, bias and the incoming output weight. Initial-value range
guards establish finite results in the recomputation and the backward stages.
The saved A value and its error are derived from the recomputation; they are not
supplied as assumptions about a forward result. The final error bounds apply to
the words actually stored by the last three stages and compare their decoded
real values with TorchLean's actual generated backward.

The conclusion gives componentwise absolute errors: one explicit bound for each
of the three sensitivities. Exceptional encodings have no invented real value;
all-bit execution existence is separate from this finite accuracy theorem.
The reference checked backward succeeds by its own proof, rather than an assumed
success premise. Bitwise PyTorch agreement and differentiation of a rounded
machine execution are different claims and are not supplied here.

The model uses serialized, single-thread affine kernels with initialized aligned
whole-word global storage, nearest-even binary32 arithmetic, gradual underflow
and the existing ISA 9.4 numeric sm_70+ feature boundary. Concrete runtime
completion, visibility and interference exclusion remain external obligations.
No PTX backward code is generated from TorchLean's automatic derivative, and no
general neural-network lowering, optimizer, loss, asynchronous stream or Gemma
implementation is claimed by this scalar example.
