# Reduction address and value origins

Every producer receives its lane number as an initial word register, converts
that number to an address register and doubles it twice. Its global load and
shared store therefore use byte offset four times that lane number. Address
and register facts must hold for arbitrary finite candidate schedules, including
candidate read values, rather than only for the selected existence schedule.

The value written into a lane's shared slot must come from that lane's actual
earlier global load. Recording the load event establishes this local origin;
the combined memory constraints separately establish that the load observed the
initialized global word. Neither the initialized value nor the desired reduction
answer may be assumed as the local store's input.

The data argument uses the fetched program and the waiting-control invariant.
A completed barrier can move all lanes to their continuation only because each
lane has reached that barrier. A change of block does not silently initialize
registers: the leader's later counter, accumulator and pointer initialization
comes from the actual move instructions. The initial lane bindings, absence of
pointer wrap, live storage and target restrictions remain explicit.
