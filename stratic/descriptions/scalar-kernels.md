# Scalar kernel proofs

The examples connect supported scalar instructions to concrete integer results.
An elementwise computation reads its inputs from an explicit memory view and
writes the modular u32 result while preserving other storage. A bounded loop
uses actual predicate and branch instructions; a decreasing measure or explicit
execution theorem establishes termination rather than treating fuel exhaustion
as success.

The kernel contracts expose all initial-register, pointer, extent, and aliasing
conditions. Completed execution, returned values, memory safety, and preservation
are proved separately where they are independent. Constructed witnesses make
execution existence explicit. Lane-wise composition operates on independent owned memory views; a shared
physical-memory and scheduling interpretation remains a separate obligation.

The source and text representations identify which PTX instruction variants the
examples use. Explanations distinguish local concrete execution from general
weak-memory execution and do not claim an unproved concurrent refinement.

A constructive relational witness links the lane example's actual memory effects
to initialized values and memory-order constraints. Register-valued store data
comes from the scalar execution. This witness is distinguished from a general
adequacy theorem for dependent concurrent programs or all hardware executions.
