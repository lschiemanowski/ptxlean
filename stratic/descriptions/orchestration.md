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

The implemented starting point is serialized work: one kernel finishes and its
stored results become the next kernel's entry memory before the next launch
begins. Each launch currently runs one thread in one global allocation, a
reserved region represented by a list of 32-bit words. There are no overlapping
launches. A concrete runtime must establish completion and visibility; a PTX
thread's exit alone does not establish either host-side obligation.

Logical storage identities distinguish successive reservations even if a future
runtime reuses the same physical address. Releasing a region permanently
invalidates its identity. Reservation takes explicit initialized contents, and
writeback replaces contents without changing the region's size or owner.

A launch checks that its allocation is live, belongs to the thread's device,
and is the region named by every supplied argument. It assembles fresh thread
state from supplied register values and argument offsets, executes the actual
instruction program to exit, and writes back that execution's final memory.
Success is not an assumed numerical result. Finite chains pass this exact store
between launches and preserve storage that the launches do not change.

The squared-affine example runs the same small program twice: first x*w+b,
then its stored result multiplied by itself with a positive-zero bias. Its
proof follows both instruction traces, establishes execution existence, and
bounds the final stored output's error against the real-valued TorchLean graph.
Asynchronous streams, concurrent launches, physical allocation and launch
interfaces, and kernels addressing several allocations remain separate work.
