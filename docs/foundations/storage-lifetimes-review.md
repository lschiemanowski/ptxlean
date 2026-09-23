# Independent storage lifetime review

The coordinator reviewed `Ptx/SequentialStorage.lean` independently of its author.
No semantic or proof blocker was found. Reviewed source SHA-256:
`17120b16cf94ba341a1d6138242dfcf7fb95b430025cbdc58e7f80a03ec46c8d`.

`Store.bounded` requires every live logical identity to precede `nextId`.
Reservation uses exactly `nextId` and increments it, with supplied initialized
contents and an explicit device owner. Neither release nor fixed-length writeback
changes the counter. These are logical generations, not physical addresses:
never-reused identifiers intentionally prevent an old handle from referring to
a later reservation. The model makes no promise that ordinary CUDA pointers
provide this protection without an additional correspondence discipline.

Release checks presence before removing exactly that cell. Writeback checks both
presence and equal length, retains the owner and identity, and changes no other
cell. The converse direction of `release_iff` reconstructs the same Store using
its fields; proof irrelevance affects only the bound proof. `Step` contains only
these three operations. `History.old_absent` propagates an old identity's absence
through every valid operation; the counter proof prevents reservation from
reusing it. `released_never_live` and `released_reallocated` therefore cover an
arbitrary intervening history, not only the next operation. Direct arbitrary
construction of another Store is not a History and is not covered.

The environment conversion derives global, initialized, readable and writable
allocation metadata from the actual live cell, with byte length four times the
word count. `access_iff` combines the device-owner check with the existing aligned,
bounded scalar access check. Release yields the unallocated result, including
after later reservations; fixed-length writeback preserves access metadata.
Zero-length reservations admit no four-byte access. Logical address offsets use
the existing 64-bit representation; this is not a physical allocator model.

The three concrete examples check replacement identity, rejected resizing and
foreign-device rejection. The public dependency inventory contains 38 explicit
declarations and is included in the ordinary root audit. The authored audit
record contains only standard Lean axioms. Final milestone checks recompile the
module and rerun those exact public dependency reports.

These are reusable serialized storage guarantees. Resource exhaustion, initially
uninitialized memory, physical address reuse, asynchronous work and a concrete
runtime's ownership/lifetime discipline remain outside the model. The Stratic
contract and guide expose these boundaries.
