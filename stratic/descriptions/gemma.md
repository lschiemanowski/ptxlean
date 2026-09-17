# Text-only Gemma 4 12B

This example supplies project-developed PTX implementations and correctness
proofs for the actual text-only Gemma 4 12B architecture. The specification
identifies the checkpoint, configuration, parameter roles and sharing, and
reference implementation used by its correspondence claims.

KV-cached forward inference verifies cache updates and their relationship to
the cache-free network, including positions, masks, and architecture-specific
state behavior.

Backward uses the cache-free forward and covers gradients for all parameters
in the transformer blocks. Embedding and unembedding weight gradients are
optional; propagation through the unembedding operation to block outputs is
required. Saved activations or recomputation can support backward without
differentiating through incremental KV-cache history.

The example exposes a general VJP interface and a concrete loss, such as cross
entropy, with explicit targets, masking, normalization, and reduction semantics.
TorchLean constructs the backward specification, while the PTX implementation
and its correctness proof are developed separately.

The implementation uses an explicit mixed-precision policy. Its contracts state
tensor and cache representations, operation-level precision, permitted
approximations, numerical error guarantees, and execution properties. PyTorch
correspondence identifies the concrete reference and configuration, including
numerically relevant choices.

The accompanying explanation follows cached forward and cache-free backward
through kernel composition. It shows how cache invariants are maintained, how
block-parameter VJPs are obtained, and how local numerical bounds contribute to
logit, loss, and gradient guarantees. Reproducible verification identifies the
supported input and resource domains and distinguishes proofs from empirical
comparisons.
