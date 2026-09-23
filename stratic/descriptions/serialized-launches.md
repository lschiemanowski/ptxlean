# Serialized launches

A serialized launch runs one kernel to completion before another command uses
its stored results. Each launch selects one live global allocation: a named
region of device memory containing initialized 32-bit words. Every supplied
memory argument carries that same allocation identity and a 64-bit byte offset.
The launch rejects a missing allocation, a different device owner, or an argument
naming another allocation, even when its numeric offset would fit.

The initial thread state starts at instruction zero. Value registers, predicates
(true-or-false registers used to guard instructions), and unused address registers
come from an arbitrary supplied seed. Argument offsets fill address registers
zero through the argument count minus one. The memory is the selected live
allocation's current contents. Fresh register state means this new assembly;
it does not require different values and does not mean implicit zero fill.
This binding is an abstract argument contract, not an implementation of PTX's
parameter-passing convention.

A successful launch contains a finite execution of the fetched mixed scalar and
binary32 program ending in thread termination. Exactly that execution's final
memory replaces the selected allocation's contents, retaining its identity,
device owner and size and preserving every other allocation. An assumed output
predicate cannot substitute for this execution. Every memory access in its trace
passes the live allocation's four-byte alignment, extent and device-owner checks.
Offset bounds need not hold for an argument that execution never accesses.

Finite chains connect the actual resulting storage of each successful launch
to its successor. Chains can be joined, and a proved per-launch storage contract
can be propagated along a chain. Such a contract theorem does not establish that
a launch exists; existence requires construction of an actual terminating run.
Releasing an allocation prevents subsequent successful launches through its old
identity, including after later storage reservations and updates.

Interpreting these abstract transitions as a real runtime requires that it wait
for completion, make preceding writes visible, keep storage live and exclude
interfering accesses. These are external correspondence obligations. PTX thread
termination and memory scope do not establish them. This first interface has
one thread and one global allocation per launch, with no overlapping launches,
asynchronous streams or general memory graph spanning kernels. Each kernel's
entry memory is a snapshot, not a new set of physical initialization writes.
