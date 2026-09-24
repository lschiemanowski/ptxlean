# Walking the shared reduction input

The leader does not start with a magically initialized loop state. Lane zero is
selected by the fetched comparison against its lane identifier. It then executes
three moves: initialize the remaining count to the CTA size, the accumulator to
zero, and the pointer to byte zero. Only then does the branch enter the loop.
Other incoming register and predicate values are arbitrary.

`Loop.LaneInvariant` describes instruction boundaries. Let `r` be the natural
number represented by the unsigned 32-bit counter, and let `k = n - r` be the
number of completed iterations. The counter never exceeds `n`. The pointer is
`4*k` at the loop's comparison, branch, load and addition. After the fetched
pointer increment (at program counter 4), it is `4*(k+1)` while the counter still
says `r`. After the fetched counter decrement (at program counter 5), `k` itself
increases and the usual pointer relation holds again. This intermediate boundary
is why the proof does not collapse two instructions into one atomic update.

The comparison at program counter 0 supplies the predicate tested at program
counter 1. A zero counter branches to the loop-exit branch at program counter 7,
which transfers to the output block; a nonzero counter reaches the load at
program counter 2. Consequently every actual load
uses slot `k < n`. The non-wrapping configuration bound `4*n < 2^32` makes the
initial counter represent `n` exactly. Counter subtraction is proved to have no
underflow at its reachable instruction boundary.

`Loop.step_preserves`, `runWith_preserves` and `reachable` establish these facts
for any candidate read oracle and finite dispatch schedule. `load_address`
extracts the counter/pointer fact at the load boundary; the emitted-event address
lemmas connect it to the exact fetched instruction and actual memory effect.
Blocked dispatches, faults and repeated scheduling of exited threads do not
invent progress.

This module proves the address and leader-control structure. It does not assert
that shared loads return the published data, that the accumulator is the sum, or
that an arbitrary scheduler eventually completes. The memory-source constraints,
actual publication history and arithmetic accumulator proof provide those separate
connections. The same fixed single-CTA program, isolated arenas, explicit relaxed
memory qualifiers and target restrictions as the parent reduction apply.

`TerminalLane` additionally records which fetched exit can halt a thread. The
follower exit is reachable only by a nonzero lane. The leader can halt only at
program counter 1 in the output block, after the output store at program counter
0 has advanced successfully. `halted_leader` exposes that final position without
assuming completion, memory contents or an expected sum. A separate output-memory
invariant can combine this position with the store's value proof to establish
what remains in global memory on completion.
