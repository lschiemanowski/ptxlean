# Live storage and allocation identities

Storage is a collection of initialized word arenas, each owned by one device.
An arena is a list of 32-bit words. Reserving one supplies its initial words and
returns a fresh logical allocation identity. Releasing it removes that identity
from live storage. Writing a completed kernel's memory back requires the identity
to be live and the word count to remain unchanged. Other allocations, the owner
and the allocation's size are preserved.

An identity names one allocation lifetime, not a physical GPU address. The store
carries a counter larger than every live identity. Reservation advances that
counter; release and writeback never move it backwards. An old identity remains
absent after release throughout every later valid sequence of these operations,
even when an equally sized arena is reserved. A replacement receives a different
identity. This prevents a stale handle from becoming valid merely because storage
was reserved again. A real allocator may reuse physical memory; relating that
reuse to distinct logical identities is an external correspondence obligation.

The allocation access environment is derived from the live word lists, rather
than maintained as a second independent table. Each live arena is global memory,
four-byte aligned, readable, writable and fully initialized by its supplied word
list. Its owner is the recorded device. A four-byte access succeeds precisely
when its logical identity is live, the issuing thread belongs to that device,
and its byte offset is aligned and within the arena. Releasing storage makes
access through its old identity fail as unallocated.

The current layer supplies storage transitions and their lifetime/access proofs.
Kernel argument binding, fresh per-launch registers and completed-run writeback
belong to launch composition. One kernel invocation will use one selected arena;
there is no claim here of arbitrary multi-allocation pointer arithmetic. Byte
offsets are already 64-bit scalar addresses, while allocation identities are
unbounded logical names. Physical address translation, allocation failure,
resource exhaustion, hardware allocation and CUDA lifetime behavior are not
modeled. Caller-supplied initial words are not implicit zero initialization.

The lifetime theorem follows a valid transition history. Arbitrarily replacing
the whole store with an unrelated freshly constructed state is not a valid
transition and carries no identity-continuity guarantee. The model has no
in-flight launches: launch composition must keep storage live through execution
and commit only after its explicit synchronous completion boundary.
