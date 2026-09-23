# Memory observations with aliased affine inputs

Three loads followed by one store can use the same memory word without allowing
an earlier load to read from that later store. This graph describes that bounded
memory pattern. The caller supplies an initial list of 32-bit words and four
valid, four-byte-aligned addresses. Any input or output addresses may coincide.
Each memory location has one initialization event, even when several arguments
name it. The graph then contains three relaxed loads at dispatch positions zero,
one and two, and a relaxed store at position five, all from one thread.

For arbitrary proposed load values, store value, source choices and write order,
the graph's validity rules force every load to observe its location's initial
word. A source choice identifies the write supplying a read. A load cannot choose
the final store: their actual position labels place that write causally after the
load at an overlapping address. The only remaining write is the unique matching
initialization. This reasoning retains output/input aliases and does not assume
the desired load values.

A valid witness is constructed for those initial load values and any store word.
Each load selects its own initialization event. The output word's initialization
precedes the sole store in write order; there are no other ordered write pairs.
All required ordering and source rules are proved. Strictly increasing event
indices rule out forbidden cycles, including when every address is the same.
The ordering proof does not assert that the arbitrary store word is arithmetically
correct; the local execution must establish that separately.

This is an abstract memory graph for the prescribed event shape. The affine
kernel separately connects its labels to all four memory events projected from
an actual fetched mixed arithmetic trace, with initialization supplied by the
initial arena. That kernel also establishes the arithmetic value stored and
forward register dataflow. Graph validity alone is not a general no-thin-air
formalization. A proved absence of cycles in this particular graph's program-order
and read-source edges is useful evidence, not an additional axiom imposed on all
PTX executions.

The source interpretation is the pinned PTX 9.4 aligned scalar u32 global-memory
fragment, with explicit relaxed GPU scope, one issuing thread, ordinary generic
memory access and a target of sm_70 or later. Arena addresses are resolved byte
offsets, not a runtime pointer-translation proof. Isolation excludes accesses by
other threads, hosts and asynchronous operations. Full-word aliases are allowed;
partial overlaps, distinct virtual aliases and mixed-width accesses are excluded.
One initial event groups the four bytes of an existing word; this reuses the
restricted memory model's normalization, not a new proof of general byte adequacy.
