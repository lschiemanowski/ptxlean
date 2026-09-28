# Parallel elementwise arithmetic

An elementwise pass assigns one output cell to each lane, where a lane is one
participating thread. All lanes fetch the same straight-line instruction program.
Each lane loads its own input and a common scalar, computes a shifted exponential
or a rounded normalization, stores the result back to its own cell, and exits.
The common scalar lies outside the output prefix. Distinct lanes never write
each other's cells. The first domain is one nonempty group of at most 1024 lanes,
using the same finite-score and numerical conditions as the reference softmax.

The machine accepts arbitrary lane interleavings and candidate load values.
Arithmetic steps reuse the existing addition, multiplication, exponential and
reciprocal instruction relations, retaining all permitted numerical outcomes.
Entry initialization sets each lane’s program counter to zero and supplies its
own-cell and common-scalar address registers. This is an explicit input interface,
not a fetched address-calculation program or a runtime launch proof. Other initial
register values are arbitrary. Every step checks actual instruction fetch and the target. An enabled exponential
outside the existing supported domain has no arithmetic step; a completed-run
proof must not assume that this missing step exists. This adapter has no barriers
or shared-memory operations. Parallel reductions retain their separate machine.

Memory admission applies the existing whole-word constraints to the actual
emitted loads and stores, with no additional cross-thread order. A read cannot
silently receive the value intended by the proof. For a lane's own input cell,
any noninitial writer would be that lane's later output store. The instruction
order places the read before that store, and the memory model forbids using a
causally later store as the source of the read. No lane writes the common scalar.
These facts derive each operand's original value for every admitted execution.
They do not restrict all executions to a globally sequential memory order.

Allocation bounds, four-byte alignment and nonwrapping addresses are checked
against actual accesses. Universal completion correctness identifies final
stored values and unchanged cells. A separate finite schedule constructs actual
arithmetic and memory steps, and derives a valid memory graph for that trace.
A witness schedule does not assert scheduler fairness or GPU progress.

Softmax uses one such pass after its parallel maximum and another after its
parallel sum. Phase boundaries retain the existing explicit waiting and scratch
initialization model; they are not a CUDA runtime implementation or fused kernel.
The new passes and the sequential reference permit exactly the same final arrays.
Both directions are proved through a contract giving each stored result’s
instruction relation and preserving all cells outside the output prefix. This
keeps the numerical allowances and initial-score accuracy guard unchanged,
without selecting a unique approximate exponential result. Masking,
arbitrary row lengths and benchmarking remain separate. The backward component
uses the existing two-input pointwise machine for its difference and product
passes; it does not require this exponential/reciprocal adapter.
