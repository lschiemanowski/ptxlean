# PTXLean

PTX (Parallel Thread Execution) is a low-level instruction language for NVIDIA
graphics processing units (GPUs). A GPU kernel is a program run by many threads.
Each thread works with values in its own small storage locations, called
registers, and can also read and write memory accessible to other threads.
A kernel's result depends both on what each thread computes and on how the
threads interact.

PTXLean describes these computations and interactions in Lean, a language in
which definitions and proofs can be checked mechanically. Its scope is the full
PTX instruction set and computing model of version 9.4. On this foundation, it
provides reusable tools for verifying neural-network implementations against
specifications expressed in TorchLean, where network computations are described
in Lean.

The PTX foundation defines the executions that NVIDIA's documented semantics
permit. This gives kernel proofs their meaning: they must account for the
behavior allowed by PTX, including cases where more than one outcome is possible.
It also makes the conditions on memory access, coordination between threads (synchronization),
and instruction use explicit.

The verification interface connects a TorchLean network specification to the
kernels that implement it. It relates the network's multidimensional arrays of values, called tensors, to
their arrangement in memory and combines the guarantees of individual kernels into a result for the
whole computation. Correctness includes both following the specified computation
and controlling numerical error relative to an ideal network over real numbers.
Exact agreement of bits and agreement within an error bound are distinct claims.

Examples show how these foundations fit together to verify concrete
neural-network implementations. They make the reusable interfaces tangible and
expose the additional assumptions and proofs required by each application.

Explanations accompany the formalization so that readers can understand the
computing model, the choices made in representing it, and the meaning of its
proofs. Study guides and worked examples connect these ideas to Lean definitions
and proof steps. Stratic links the project's descriptions to the implementation
and evidence supporting them, and verification can be reproduced.

Every result distinguishes what is proved, assumed, tested, or still unsupported.
Lean checking establishes that a proof follows from its definitions; whether
those definitions faithfully represent PTX is a separate question. A correct
result on completion, the existence of an execution, and guaranteed termination
are also separate promises. Any further connection to a compiler that translates the program, the runtime
software that manages memory and launches kernels, or a physical GPU states
the additional justification it requires.
