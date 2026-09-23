# Multi-kernel orchestration

Orchestration coordinates work split across several GPU kernels. It describes
which memory regions are reserved (allocations), when kernels begin (launches),
and which earlier results must be ready before later work can use them
(dependencies). Storage lifetime is the interval during which a region remains
available. The model connects each kernel argument to the intended memory buffer, a region
holding its data, and establishes both the required execution order and the reader's ability to
observe earlier writes. It covers values retained across calls as well as
temporary intermediate results.

The orchestration layer combines permitted kernel executions while preserving
the assumptions needed for their safety and execution guarantees.

Individual kernel proofs are combined under contracts for the runtime, the
software that reserves memory and launches GPU work. Showing that a particular
runtime, memory allocator, or launch interface obeys those contracts is a
separate proof obligation. The combined theorem retains its assumptions about
who may access storage, pointers that name the same storage (aliasing), and
available resources.

Explanations follow data from allocation through producer and consumer launches
to its final observation or release. They show where ordering, visibility, and
lifetime obligations arise and distinguish abstract orchestration guarantees
from assumptions about the executing runtime.
