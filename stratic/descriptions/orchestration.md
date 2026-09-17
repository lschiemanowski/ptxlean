# Multi-kernel orchestration

The orchestration model describes allocations, kernel launches, dependencies,
storage lifetime, and observable results. It accounts for argument and buffer
correspondence and establishes the ordering and visibility required by consumers
of intermediate results. It supports persistent state across calls as well as
temporary values shared between computations.

The orchestration layer composes permitted kernel executions while preserving their safety and execution premises.

Correctness of individual kernels is composed under explicit runtime contracts.
Correspondence between those contracts and a concrete runtime, allocator, or
launch API is a separate obligation. Ownership, aliasing, and resource premises
remain visible in the resulting composition theorem.

Explanations follow data from allocation through producer and consumer launches
to its final observation or release. They show where ordering, visibility, and
lifetime obligations arise and distinguish abstract orchestration guarantees
from assumptions about the executing runtime.
