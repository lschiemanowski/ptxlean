# Scalar kernel proofs

The examples connect scalar instructions to concrete integer results. Elementwise
computation applies an operation to corresponding array elements. It reads them
from specified memory locations and writes the `u32` result, wrapping modulo
`2^32`, while preserving other storage. A bounded loop uses actual conditional
and branch instructions. A decreasing quantity or an explicit execution proof
establishes that it finishes; exhausting the evaluator's step budget does not.

The contracts state initial register values, pointer addresses, available memory
size, and conditions on addresses that refer to the same storage (aliasing).
Completion, results, safe accesses, and unchanged memory are proved separately
where they are independent. A constructed execution proves existence. Per-thread
results over independent memory lists are distinguished from results for threads
sharing one allocation under a scheduler.

The source and text representations identify the instruction forms used.
Explanations distinguish a concrete local run from the wider range of memory
observations PTX can permit across threads, often called weak-memory behavior.
A proof for the former is not silently treated as a proof covering the latter.

For the addition example, a constructed memory graph records the actual reads
and writes, their initial values, and the proposed source and ordering relations.
A proof connects this graph to the instructions that ran. Store data comes from
the computed registers. This does not establish that the combined model captures
every dependent concurrent program or every hardware execution.

The shared-allocation vector-add example runs distinct threads against one memory
state. Each thread has its own output location, so their writes cannot interfere
with one another. The proofs establish correct completed results and construct
an execution that finishes.

## The bounded sum contract

The sum kernel repeatedly tests a count, loads one word, adds it to a running total called an accumulator,
advances a byte pointer by four, decrements the count, and branches back. Zero
count branches to explicit exit. The reference result adds the requested contiguous portion of memory (the slice)
one word at a time modulo `2^32`, starting from the supplied accumulator.
For example, the slice `[2, 3]` with accumulator `10` yields `15`; overflow wraps.

Execution begins at instruction zero with the count in value register 0, the
accumulator in value register 1, and byte pointer `4*start` in address register 0.
The required bounds are `start + count ≤ memory.length`, `count < 2^32`, and
`4*(start + count) < 2^64`. The last is a sufficient bound that also covers the
pointer immediately after the last word, even though it is not read. The theorem proves explicit halt and the reference result in
`7*count + 3` dispatches with unchanged memory. More fuel preserves the same
completed result. Access safety is proved separately; it alone would also hold
for a safe prefix that later faults. This loop's result is sequential and has no
general theorem connecting its traces to all permitted concurrent PTX behavior.
