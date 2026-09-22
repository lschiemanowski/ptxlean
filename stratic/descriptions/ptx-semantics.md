# PTX semantics

The authoritative semantics describes permitted PTX executions. Local
instruction behavior uses operational rules; memory consistency uses Lean
predicates expressing the axiomatic constraints on observations and ordering.
Executable simulators and derived kernel proof rules have explicitly justified
relationships to this semantics.

Coverage encompasses the full PTX ISA 9.4 instruction set and computing model:
arithmetic, control flow, state spaces, concurrency, memory, synchronization,
collective participation, and asynchronous operations. It includes legal
variants, types, qualifiers, version conditions, and target restrictions.

Instruction effects, thread control flow, collective participation, memory
events, and asynchronous initiation and completion constrain one another.
The model preserves documented execution freedom, including weak memory
behavior, thread scheduling, and asynchronous effects.

Semantic fidelity is supported by source-linked interpretations, internal adequacy results, and independent evidence, separately from Lean proof checking.

Undefined behavior, target/version illegality, and missing formalization
coverage are distinguished. Unsupported cases cannot silently produce an empty
execution relation that makes universal correctness vacuous.

Safety, correctness of completed executions, execution existence, and progress
or termination have separate statements with explicit scheduling, fairness,
resource, and environment premises. Derived rules for ownership,
synchronization, and tensor operations follow from the underlying semantics.

Explanations relate the formal rules to the programming and computing model in
[NVIDIA's PTX manual](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html).
Examples show how scheduling, memory ordering, and asynchronous completion
permit or prohibit behaviors, and identify which assumptions a kernel proof
must establish.

A scalar message-passing fragment connects straight-line instruction execution to scoped memory relations and proves publication and counterexample results under explicit restrictions.

An explicit execution environment represents thread topology, memory scopes,
address spaces, storage ownership, and instruction eligibility. Scalar execution
connects register and predicate state, control flow, addresses, and memory effects
to complete kernel proofs with stated execution and memory-model boundaries.
