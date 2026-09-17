# TorchLean and kernel verification interface

The interface relates a TorchLean network specification to concrete kernel
implementations, including compositions of multiple kernels. Logical tensors
and state are related to their concrete storage representations across
alternative layouts, mixed precision, intermediate storage, and stateful
operations.

Layout correspondence and numerical approximation are separate obligations.
Kernel contracts state input representations and preconditions, the specified
computation, and output representations and guarantees. Different layouts,
fusion strategies, and schedules can realize the same logical responsibility.

Orchestration contracts account for allocations, launches, dependencies, storage lifetime, and observable results across kernels.

Numerical contracts distinguish real-valued meaning, floating-point behavior, bounded error, and correspondence with a concrete PyTorch implementation.

Backward specifications are constructed automatically in TorchLean; PTX backward implementations and their correctness proofs are supplied separately.

Composition requires a producer's guarantees to satisfy its consumer's
requirements, including ownership, lifetime, synchronization, and numerical
conditions. Network-level proofs use these contracts without re-establishing
instruction-level facts at every composition boundary.

Interface explanations show how a logical tensor relates to stored values,
which obligations change with a layout or precision choice, and how individual
kernel guarantees combine into a network-level claim. They identify the exact
TorchLean definitions and the hypotheses used in each correspondence theorem.
