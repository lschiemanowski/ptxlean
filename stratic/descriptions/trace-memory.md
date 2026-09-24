# Actual traces and memory events

A thread may visit the same instruction many times in a loop. Each visit is a
separate occurrence. This interface numbers all visits in the order they happen,
including arithmetic, branches and skipped instructions, before selecting memory
accesses. An instruction address therefore never stands in for execution order.

A projection uses the issuing thread and selects the memory access recorded by
each occurrence. It retains
the original occurrence, its dynamic position, its read or write ordering, its
value, and its storage location. The interface proves both directions: every
projected access comes from the trace, and every access identified by the
projection appears exactly once at that position. An adapter to an instruction
machine must separately prove that its projection identifies exactly the actual
memory effects of the fetched instructions. An arbitrary projection function
alone does not establish that a program ran.

Storage is identified by a catalogue of distinct live allocations. A global
allocation and a shared allocation owned by a cooperative thread array (CTA)
are different catalogue entries even when their numeric addresses agree. Shared
storage carries the device, grid, cluster and CTA identities, so equal local CTA
numbers in different grids cannot accidentally identify the same storage. Each
access names one entry and a word offset, the number of four-byte words from its
start. The graph address encodes that pair injectively: equal graph addresses
mean equal entries and equal offsets. Translation from a computed byte address
must separately establish alignment, bounds, ownership and a live allocation;
the encoding itself grants no permission and resolves no physical aliases.

Initial writes describe the starting value of each represented word. They precede
the concatenated per-thread projections in one event list. Read-source and write-
ordering choices cannot change these event labels. Program order is preserved
across storage spaces; accesses to global and shared memory are not split into
independent graphs. Initial locations must be unique, and each participating
thread must appear once when assembling a concrete candidate.

Changing event numbering or injectively renaming storage addresses must preserve
the memory rules. Transport proofs provide that guarantee, including read-source
choices, write ordering and any separately justified synchronization edges.
The ordered global scalar adapter recovers the earlier publication event labels
exactly, so those existing proofs apply to the common projection.

The graph checks are necessary memory constraints for this restricted use:
aligned whole-word accesses, ordinary generic memory access, and strong operations
that mutually include the participating threads in their scopes. A graph passing
these checks is not a sufficient admission test for arbitrary PTX programs whose
reads influence later values, addresses or branches. Concrete execution proofs
must also justify every synchronization edge and give a separate constructive
argument that their witness computations have grounded inputs. General PTX
no-thin-air behavior, mixed-size accesses, physical aliases, asynchronous accesses
and hardware execution remain outside this interface.
