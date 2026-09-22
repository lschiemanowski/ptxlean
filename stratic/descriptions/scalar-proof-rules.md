# Scalar verification rules

Reusable rules connect local instruction transitions, sequential execution
segments, invariants, and completed runs. A rule states whether it establishes
partial correctness, finite-prefix safety, or termination. Composition preserves
explicit program-counter and outcome conditions; fuel exhaustion is never
silently promoted to termination.

Memory preservation is expressed through actual store effects and disjoint
locations. Frame arguments cannot assume the desired final memory or ignore
interference. The rules support branching loops and instruction-level kernel
proofs while retaining the scalar machine's concrete/candidate distinction.
