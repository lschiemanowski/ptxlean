# Examples

Examples range from small kernels that exercise one reusable contract to concrete
network implementations that combine the contracts. A small kernel makes the
connection between instructions, stored values and checked guarantees easier to
follow. A network example reaches from its specified computation to the stated
kernel behavior, giving an end-to-end verification result. Each example identifies
its computation, inputs, state kept between calls, number-format and approximation
choices, and execution assumptions. Network examples also identify their
architecture: the arrangement of network operations.

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
