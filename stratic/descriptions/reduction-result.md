# Reduction accumulation and output

The leader starts its counter, accumulator and shared pointer by executing the
program's move instructions. Its loop then loads successive shared words and
adds each word to the accumulator with unsigned 32-bit wraparound. A partial
execution has accumulated a precise prefix of the inputs, taking account of
whether its current iteration has already executed the add or the decrement.
The global output store uses that actual accumulator register.

The arithmetic argument needs a precise memory obligation: every actual shared
load at an input slot must observe that input word. This is a condition on emitted
memory events, not an assumed sum or final register. The combined candidate graph
must discharge it from source selection, publication order, and the actual
producer load-to-store value connection. A memory-validity proof and an arithmetic
loop proof remain separate, and their final composition must not retain this
read-value condition as an unexplained assumption.

The result applies to arbitrary finite schedules and candidate observations.
Stopping early need not produce an output. Any actual output store must contain
the full modular sum. When the leader finishes, the global allocation contains
that sum in its output slot and retains every other word. A supplied complete
schedule separately establishes execution existence. Pointer bounds come from
the fetched initialization, loop counter and cursor updates; extra allocated
scratch words are not a reason to permit additional iterations.
