# Examples

Examples demonstrate end-to-end verification by connecting a concrete network
specification, its kernel implementation, and checked correctness results through
the reusable PTX semantics and verification interface. Each example makes its
architecture, inputs, state, numerical policy, and execution assumptions explicit.

The Gemma example verifies text-only Gemma 4 12B implementations for KV-cached forward inference and cache-free forward/backward computation.

An example explains how to reproduce its verification, how its proof is
assembled, and which claims concern mathematical correctness, numerical
accuracy, implementation correspondence, or execution. Supporting experiments
are identified separately from checked results. Examples illustrate both the
use of reusable contracts and the application-specific obligations that remain.

An example's coverage is stated for its own architecture and execution domain;
it does not define the coverage of the underlying PTX formalization. Its
explanation connects concrete tensors, storage, kernels, and state transitions
to the abstractions used by the verification infrastructure.
