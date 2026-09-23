# Storage and valid memory accesses

An allocation is a reserved region of memory. Its size in bytes is its extent.
The complete value being read or written must fit inside it. For example, a
four-byte read starting at byte 12 fits in a 16-byte allocation; one starting at
byte 14 extends beyond its end.

An access can also require a suitably positioned starting address, called
alignment. A four-byte aligned access begins at an address divisible by four.
The caller supplies an alignment guarantee for the allocation's starting address;
the checker combines this with the distance from that start, called the byte
offset. Even when enough bytes remain, an unsuitable offset can fail alignment.
A failed guarantee does not prove that the physical address is misaligned.

The caller also states who may access the allocation, whether reading and writing
are allowed, and whether its initial contents are known. Together these supplied
facts form an access contract. The checker verifies that the allocation exists
and matches the requested kind of storage, the thread is allowed to use it,
the requested positive number of bytes fits,
alignment is established, and the requested read or write has permission.
Reads additionally require known initial contents. Missing that knowledge is a
failure to satisfy this contract, not a claim that PTX forbids every read of
unknown contents. The model never silently replaces unknown contents with zero.

PTX distinguishes kinds of storage, called state spaces. The represented access
rules are:

| State space | Who may use it |
| --- | --- |
| Global | Threads allowed by the allocation's system-wide or single-device ownership |
| Shared | Threads of the owning CTA; an explicitly requested access can also reach a peer CTA in the same cluster |
| Local | The owning thread only |
| Entry parameters | Threads of the grid receiving these read-only kernel arguments |

Reaching a peer CTA's shared storage also requires that the peer remain active
for the access; the checker does not establish this. A resolved address names
the state space, the allocation, and a byte offset within it. Determining that
address from a physical GPU pointer remains outside the model, as do creating
and releasing allocations and handling different pointers to the same storage
(aliases). These assumptions must be justified when connecting to the software
that manages allocations and launches kernels, called the runtime.

## Connecting allocation checks to scalar execution

The scalar interpreter executes individual thread instructions over a list of
four-byte values, called words. This list is its memory arena. A theorem relates
its alignment and bounds checks to the access contract for one global allocation
with known initial contents. Every memory access recorded by an interpreter run
satisfies that allocation's contract. This does not establish how other threads observe
its writes or how an actual runtime launches the kernel.

The allocation connection also covers recorded accesses in runs that later fail
or reach their step limit. It is a safety guarantee, not a proof of termination.
Different allocation identifiers name different storage in the resolved-address
model; relating these identifiers to physical addresses is a separate obligation.
