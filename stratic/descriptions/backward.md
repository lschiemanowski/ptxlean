# Backward specification and verification

For a supported differentiable real-valued network `F`, the backward target is
the vector-Jacobian product `DF(x)^T * y_bar`. The selected input and parameter
variables and incoming cotangent are explicit. This interface supports
composition without constructing a full Jacobian or fixing a loss.

TorchLean constructs the backward computation automatically, with checked
correctness results connecting it to the mathematical VJP under explicit
hypotheses. The supported operations and applicable theorem boundaries are
identified for each use of this construction.

The PTX backward implementation is authored separately, together with its
correctness proof. Reusable lemmas, tactics, and model assistance support that
proof; automatic differentiation of the TorchLean specification does not
synthesize the PTX implementation or establish its correctness.

Mathematical differentiability and backward correctness, numerical accuracy,
kernel correspondence, and execution existence, safety, and termination have
separate proof obligations. A constructive backward specification does not
itself establish termination of its kernel realization.

Explanations trace the incoming cotangent through the specified backward
computation and its kernel contracts. They identify the differentiated variables,
saved-value or recomputation requirements, differentiability hypotheses, and
numerical and execution guarantees supplied by each theorem.
