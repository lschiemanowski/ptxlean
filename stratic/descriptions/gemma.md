# Text-only Gemma 4 12B

This example supplies project-developed PTX implementations and correctness
proofs for the actual text-only Gemma 4 12B architecture, meaning its specific
arrangement of network operations. The specification identifies the saved model
weights (the checkpoint), configuration, parameter roles, any weights reused in
multiple places, and the reference implementation used for comparisons.

Forward inference computes network outputs. A key/value (KV) cache stores
attention keys and values from earlier tokens for reuse on later calls. The
proof relates cache updates to a forward computation without the cache, including
token positions, masks that exclude particular attention connections, and the
architecture's specific rules for state changes.

Backward computes derivatives using the forward computation without the cache.
It covers gradients, the derivatives with respect to parameters, for every
parameter in the transformer blocks, the repeated attention and feed-forward
stages. The embedding converts token identities to vectors; the unembedding
converts final vectors to output scores. Derivatives with respect to those two
operations' weights are optional, but derivatives must still pass through the
unembedding to the block outputs. Intermediate forward values, called activations,
may be saved or recomputed. The proof does not differentiate through the history
of incremental cache updates.

The example exposes a vector-Jacobian product (VJP) interface: given weights on
the network outputs, backward returns the derivatives of their weighted sum.
It also provides a particular scalar objective, or loss, such as cross entropy,
which penalizes assigning low probability to the target token. Contracts specify
the targets, which positions count, and how terms are scaled and combined into
a single loss. TorchLean constructs the backward specification; PTX code and
its correctness proof are developed separately.

The implementation specifies which number format each part uses; using different
formats within one computation is mixed precision. Contracts state tensor and
cache layouts, operation-level precision, permitted approximations, error bounds,
and execution properties. PyTorch correspondence identifies the concrete reference
and configuration, including choices that change numerical results.

The explanation follows cached forward and cache-free backward through their
kernels. It shows how properties that must remain true of the cache, called cache
invariants, survive updates, how block-parameter derivatives are computed, and how
local error bounds combine into guarantees for output scores (logits), loss, and
gradients. Reproducible verification states the supported input and resource
conditions and distinguishes proofs from measured comparisons.
