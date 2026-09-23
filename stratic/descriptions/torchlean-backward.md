# Checked TorchLean backward construction

This bridge uses TorchLean's own representation of a computation as a graph:
each step takes previously computed tensors and produces another tensor. A tensor
is a multidimensional array. The graph records the local derivative rules needed
to propagate output weights backward to chosen inputs and parameters. Composing
these rules constructs the backward computation without writing a separate
backward formula for each complete network.

Each primitive rule must have a checked proof that it is the mathematical
derivative of its forward operation. Operations with restricted derivative
domains, such as a reciprocal away from zero, retain those conditions at the
actual intermediate values. The proof graph must describe the same operations
and data as the graph whose backward computation is evaluated.

For an arbitrary tensor of output weights, the bridge establishes both that the
chosen exact backward computation succeeds and that its returned input and
parameter sensitivities are the mathematical vector-Jacobian product. A theorem
that assumes successful evaluation supplies correctness conditional on success;
a separate proof must establish that success under the stated input conditions.
The lower-level exact tape, which stores forward values and local backward rules,
and the checked application interface can have different success conditions.

The first example computes a pointwise affine transformation followed by squaring:
each output coordinate is `(input * weight + bias)^2` at that coordinate.
Its weight and bias values are differentiable inputs rather than fixed graph
data. The input shape and the output-weight shape are explicit. It uses actual
upstream graph constructors and derivative proofs, so that an independently
recreated toy language cannot satisfy this example.

The PTX foundation and integration package use a compatible pinned Lean version.
The integration imports the actual PTX package together with the pinned upstream
TorchLean and mathlib packages. A small shared theorem connects the unsigned
value of the modeled PTX minimum operation to a real scalar tensor; this checks
that definitions and proofs from both libraries can be used together. It does
not identify a PTX kernel with a TorchLean network. The generated-backward proofs
retain their separate exact-real meaning and explicit parameter boundary.

These results concern exact real-valued graph semantics. They do not establish
floating-point accuracy, correspondence with a concrete PyTorch implementation,
or safety and termination of separately authored PTX kernels. Those obligations
remain separate even when the exact backward computation is proved to succeed.
