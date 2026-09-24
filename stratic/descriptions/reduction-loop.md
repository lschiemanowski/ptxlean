# Reduction loop addresses

The leader walks through the shared input slots in order. Its counter records how
many slots remain, and its byte pointer records the next slot to read. These
values come from the program's actual initialization and update instructions;
other incoming registers and predicates may be arbitrary.

Every reachable shared load belongs to lane zero and addresses slot k with
0 ≤ k < n. The counter is positive at a load. After the pointer increment but
before the counter decrement, the pointer is one slot ahead; the invariant
records that intermediate state rather than treating the pair of instructions
as one atomic update. The exit branch is taken only with a zero counter. A halted leader has passed
its actual output store; followers can exit only at their distinct follower
exit instruction.

This establishes address and control structure for arbitrary candidate reads
and scheduling. It does not assume that a load returns the published value,
that the accumulator is correct, or that a scheduler eventually runs the leader.
Memory source constraints and the arithmetic result are separate connections.
