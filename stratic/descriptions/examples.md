# Examples

Examples connect a particular network specification to its kernel implementation
and checked correctness results through the reusable PTX semantics and
verification interface. This is end-to-end verification: the proof reaches from
the specified network to the stated kernel behavior. Each example identifies
its architecture (the arrangement of network operations), inputs, state kept
between calls, number-format and approximation choices, and execution assumptions.

The Gemma example verifies text-only Gemma 4 12B. Its forward inference, which
computes outputs, retains attention keys and values from earlier tokens in a
key/value (KV) cache. Its backward computation, which computes derivatives,
uses a forward computation without that cache.

An example explains how to reproduce its verification, how its proof is
assembled, and which claims concern mathematical correctness, numerical
accuracy, implementation correspondence, or execution. Supporting experiments
are identified separately from checked results. Examples illustrate both the
use of reusable contracts and the application-specific obligations that remain.

An example's coverage is stated for its own architecture and execution domain;
it does not define the coverage of the underlying PTX formalization. Its
explanation connects concrete tensors, storage, kernels, and state transitions
to the abstractions used by the verification infrastructure.
