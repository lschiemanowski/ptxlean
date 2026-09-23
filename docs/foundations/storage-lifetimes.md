# Keeping an allocation live across sequential work

[`Ptx/SequentialStorage.lean`](../../Ptx/SequentialStorage.lean) models initialized
word arenas and their logical lifetimes. It does not implement a GPU allocator.
The layer is small enough to inspect without the floating-point integration:
reserve some supplied words, use or replace their contents, then release them.

## An identity names one lifetime

Suppose the first reservation returns identity zero with one word containing
17. Releasing it removes identity zero. Reserving another one-word arena with
value 23 returns identity one. An old handle `(allocation 0, byte offset 0)` must
stay invalid; the new handle `(allocation 1, byte offset 0)` names the replacement.
Equal byte offsets and equal allocation sizes do not make them the same object.
`reallocation_example` checks these exact identities and contents.

A `Cell` contains its device owner and its list of 32-bit words. A `Store` holds
optional cells indexed by natural-number identities and a counter `nextId`.
Its `bounded` proof says that no identity at or above the counter is live.
Consequently `reserve_fresh` derives that the next identity is unused. Reservation
installs the supplied cell there and increases the counter. The counter does not
wrap; it is a logical natural number, not a machine pointer.

Release requires a live cell. Writeback also requires a live cell and exactly
the same number of words. It preserves the device owner and every other cell.
`resize_rejected` demonstrates that writing two words back to a one-word cell
fails. No operation fills unknown data implicitly with zero. The initialization
contract comes from the complete word list supplied at reservation.

## Why checking immediate absence is insufficient

The important lifetime question is what happens after more operations. Merely
proving that release removes a cell would still allow a later reservation to
revive its old identity. Here `Step` represents exactly a reservation, successful
release, or successful fixed-size writeback. `History` contains any finite
sequence of those steps, including an empty sequence.

`Step.counter_mono` proves that each operation preserves or increases the
counter. `Step.old_absent` proves that an already issued, absent identity cannot
become live in one step. For reservation, it differs from the fresh counter;
release cannot create a cell; writeback cannot target an absent identity.
`History.old_absent` extends the argument to the entire history.

`released_never_live` therefore keeps a released identity absent after arbitrary
later operations. `released_reallocated` goes further: after any such history,
a new reservation returns a different identity, leaves the old identity absent,
and contains the newly supplied words. This is the proof preventing an old handle
from becoming valid after a same-size replacement. It is not an assumption that
the caller avoided later reservations.

Continuity is a property of this valid transition history. A client can construct
an unrelated empty `Store` value, but replacing a running store with it is not one
of these transitions. The proof does not claim identity continuity across that
unrelated reset.

## Access checks come from live contents

`environment` derives the existing `Ptx.Environment` allocation table from live
cells. Each cell supplies a global allocation with four-byte base alignment,
read/write permission, its recorded device owner, and exactly four bytes per
word. Its initial contents are known because its word list is present.
There is no second independently mutable metadata table to become inconsistent
with those contents.

`access_iff` proves that a four-byte access through a live identity succeeds
exactly when the thread is on the owning device and its byte offset satisfies
`Scalar.ValidAddress`. That predicate requires four-byte alignment and room for
the complete word. Device ownership and valid offsets are separate conditions;
`foreign_device_rejected` gives a concrete rejected access at offset zero from
the wrong device.

`access_absent` returns the existing `unallocated` diagnostic for a missing
identity. `released_access_fails` combines it with the history theorem, so the
same rejection holds after later operations too. These diagnostics describe
failures of this allocation contract, not a complete classification of PTX
undefined behavior or hardware faults.

`writeback_environment` proves that successful writeback leaves the derived
allocation metadata exactly unchanged. The word values can change, but size,
ownership and permissions do not. A kernel that preserves arena length can use
this property when its final memory is committed by a launch wrapper.

## Connection to launches and the external runtime

A launch must bind each argument to the intended live identity before using its
64-bit byte offset in the scalar evaluator. The storage module does not create
fresh register state or execute a kernel. Those belong to launch composition,
which must keep the selected cell live throughout execution and write its actual
final memory back only at the specified synchronous completion boundary.

The planned invocation boundary selects one arena. This is not arbitrary
multi-allocation pointer arithmetic. Logical identities may differ even if a
real allocator reuses the same physical address. Mapping that reuse to distinct
logical lifetimes is a runtime correspondence obligation; naked physical pointer
bits alone do not provide stale-handle detection. Physical address translation,
resource exhaustion, allocation failure and CUDA allocation semantics remain
outside the model. This storage history has no in-flight launches or asynchronous
accesses.

The description was recorded before implementation. `lake build
Ptx.SequentialStorage` passes, and the [public-declaration dependency audit](storage-lifetimes-audit.txt)
checks all 38 explicit public declarations. Dependencies are limited to Lean's
standard axioms. These proof checks establish the stated abstract contracts;
conformance of a concrete runtime remains a separate obligation.
