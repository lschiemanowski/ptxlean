# Vector addition in a shared allocation

Each lane is one logical worker, modeled as a distinct thread, computing one
output element; it is not a claim about a hardware warp position. Every lane
executes load, load, add, store, and exit against one shared memory allocation.
A word is a four-byte value. Each lane reads designated input words and is the
only writer of its output word. Input/output separation and distinct outputs
are built into the representation or proved. Initial registers and memory are
supplied inputs.

The scheduler chooses one lane to execute one instruction at a time. Different
choices produce different interleavings of the lanes' steps. Properties preserved
by every step, called invariants, show that a lane cannot change another lane's
inputs or output, that completed lanes return the sum modulo `2^32`, and that
accesses remain within the allocation. A particular schedule is constructed to
finish. This does not prove scheduler fairness, meaning that no lane is forever
denied execution opportunities, or progress of physical GPU hardware.

Records of reads and writes, called memory events, come from the actual executed
instructions. A proof connects these records to a graph satisfying the restricted
memory rules, including its proposed source writes and ordering. Scope, address,
initial-value, and dependency restrictions remain explicit. The machine that
interleaves these steps is not asserted to describe every PTX behavior.

## Layout and execution contract

For `n` lanes, lane `i` reads words `3*i` and `3*i+1` and writes word `3*i+2`.
Word `j` has byte address `4*j`. This interleaved layout makes ownership and
input/output separation immediate; it is not an optimized tensor layout.
The instruction sequence loads into registers 0 and 1, adds modulo `2^32` into
register 2, stores that register, and exits. All accesses use global memory and relaxed ordering at GPU scope, including
threads on that device without a release/acquire synchronization pair. They use
the ordinary memory-access mechanism called the generic proxy. Addresses are fixed for each lane; initial
memory and register values are arbitrary supplied inputs.

The execution-level bounds are `3*n ≤ memory.length` and `12*n < 2^64`.
They ensure that all accessed words exist and their byte addresses do not wrap.
They are sufficient conditions, not a characterization of every legal allocation.
There is one memory list and, for each lane, its own register values and an
instruction cursor recording how far it has advanced. Scheduling a lane advances one instruction; scheduling a completed lane
leaves the state unchanged. A cursor reaches completion only after exit executes.

## Why the result survives interleaving

Every output location differs from every input location, and distinct lanes have
distinct outputs. Thus a store cannot change anyone's input or another lane's
output. The invariant records unchanged inputs, the original values after each
load, their modular sum after addition, and the stored result after the store.
These facts are derived step by step; the final answer is not assumed at entry.
All finite schedules preserve the invariant and non-output words. Completed
schedules have every correct output. The bounds additionally justify that the
specialized steps are actual scalar-instruction steps and that accesses are safe.

Visiting every lane in five rounds constructs a completed execution with `5*n`
instruction dispatches, including the empty case. An unfair schedule can repeatedly choose
one lane and leave another unfinished. Existence and correctness of completed
executions therefore remain distinct from a claim that all schedules finish.

## Connecting execution to the memory model

The central result, `verified_shared_execution`, constructs one schedule with an
actual scalar execution, completed lanes, correct outputs, a valid restricted
memory graph, and matching per-lane event descriptions from the trace, the record of executed
instructions.
Each lane contributes two loads and one store at instruction positions 0, 1,
and 3. The graph also contains the three initialized words accessed by each lane, its memory footprint,
whose values are tied to actual allocation cells. Initial events for unused memory after the footprint
are omitted from the graph; preservation of non-output storage is proved for the
execution separately.

A separate universal statement constrains the fixed candidate family: compatible
read sources force both inputs to come from initialization, since no program
store targets an input. The register addition then forces the output sum for
any such candidate, without assuming that answer. Outputs are never read, so
these stores cannot circularly justify input values. This grounds the read values in memory contents that exist independently of
the computed outputs. It does not characterize arbitrary dependent PTX
programs, establish all hardware executions, or supply a runtime launch mapping.
