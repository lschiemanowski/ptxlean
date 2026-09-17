# PTXLean

PTXLean provides a Lean formalization of the full PTX ISA 9.4 and reusable
infrastructure for verifying neural-network implementations against TorchLean
specifications. Correctness encompasses both correspondence with a specified
computation and numerical accuracy relative to a real-valued network.

The PTX foundation describes permitted executions of the instruction set and computing model, with an explicit relationship to NVIDIA's documented semantics.

The verification interface connects TorchLean specifications to tensor representations, orchestrated kernels, and PTX executions.

Examples demonstrate how the reusable semantics and verification interfaces establish correctness of concrete neural-network implementations.

The formalization is accompanied by explanations, examples, and a study guide
connecting the computing model to Lean definitions and proofs. Each
responsibility explains its abstractions, assumptions, and guarantees at the
level needed to understand and use it. Stratic connects those descriptions to
the implementation, proofs, and explanatory material that substantiate them.

Verification is reproducible, and claims distinguish what is proved, assumed,
tested, or unsupported. Proof validity is distinct from fidelity of definitions
to the intended semantics. Bitwise equality, bounded numerical agreement,
execution existence, and termination are distinct guarantees. Compiler,
runtime, and hardware correspondence obligations remain explicit wherever a
result depends on them.
