# Independent cooperating groups

A grid is a collection of cooperating thread arrays (CTAs) launched together.
Each group contains threads with their own registers and instruction positions.
All groups access the same global memory. Each group has its own shared scratch
memory and barrier state; the same shared-memory address in two groups names
two different locations. Completing a barrier releases only its own group.

A grid step selects one group and one of its threads, fetches its instruction,
and uses the existing mixed integer and floating-point instruction semantics.
The selected group sees the actual current global array. Its resulting global
array becomes the grid's global array, while its local state is written back.
Other groups retain their registers, scratch memory and barrier state. Their
next instruction sees the updated global array. This is instruction-level
interleaving, not atomic execution of a whole group.

Candidate load values remain unrestricted until memory admission. Successful
address checks establish alignment and bounds, not the value a load may observe.
The combined memory graph must distinguish group-local storage and actual
thread identities, and derive barrier ordering from each group's executed
arrivals and completions. Admission must not be replaced by a requirement to
read the current array.

For finite execution witnesses, a selected schedule may read the current arrays.
A checked replay must then recover every read's last preceding store, or its
initial cell, across the combined trace. Giving those stores chronological
order supplies a sufficient memory-admission certificate, including actual
within-group barrier edges. This construction does not change the permitted
candidate reads or assert that every admitted execution follows that schedule.
The dense witness runs one group at a time. Within that group it executes each
lane's product segment, completes the barrier, repeats the reduction segments
and their barriers, and then executes the output segments and exits. Physical
lane numbers select registers and barrier participants; logical row-and-column
indices determine arithmetic and addresses. The construction must prove both
parts agree, without applying the 1,024-thread group limit to the grid total.
Address-representation and allocation bounds still apply.

For the independent-group fragment, common operands are read-only and writable
outputs have separate owners. These restrictions require proofs for actual
fetched addresses. The absence of interference must justify combining local
results into stored grid results. A selected finite schedule supplies execution
existence separately from universal correctness of completed admitted runs.
No fairness, simultaneous hardware execution, CUDA runtime behavior or
inter-group synchronization is promised.


For programs using only global memory and no barriers, the proof can give every
(group, thread) pair a unique flat thread number. Flattening preserves every
fetched instruction and actual global-memory update; it introduces no hardware
thread group and no new synchronization. This permits reuse of the existing
memory graph and independent-thread arithmetic proofs. Shared-memory or barrier
programs cannot use this simplification: they retain private storage identities
and group-specific arrival histories.

For pointwise copy, multiplication and ReLU sensitivity gating, every completed
admitted grid execution stores the specified result, preserves the source words
and the allocation length, and uses aligned addresses within allocated storage.
A separate theorem constructs such an execution for every input word sequence
that meets the storage bounds. The total thread count can exceed 1,024; each
group has at most 1,024 threads. For a partially used final group, spare lanes
read an explicitly allocated source word and write distinct padding outputs.
Those outputs require allocated storage and are excluded from the logical
vector; they are not promised to retain their initial contents. Zero groups
have an explicit no-launch case.

A composed pointwise stage uses groups of 32 lanes. Its host-side storage view
appends enough spare output cells to fill the last group, runs the actual padded
launch, and returns the original-length prefix. Every logical output and source
word remains in that prefix. The proof accounts for the larger physical array;
discarded padding cells are neither gradients nor preserved application data.
This allocation-and-view operation belongs to the host model, not a proved
CUDA memory allocator.

The row-distributed dense program has a complete launch contract. Every completed
admitted combined execution stores the prescribed reduction results, preserves
its operands, and performs aligned accesses within allocated arrays. Its proof
derives input reads, scratch producers, barrier ordering and unique output
writers from that same trace. A separate finite construction reaches every
thread's exit and supplies read sources and write ordering satisfying the
combined memory constraints. It also covers an empty grid.

The backward composes five actual launches: recompute the forward activation,
gate the incoming sensitivity, multiply weight gradients, copy transposed
operands, and reduce input gradients. Each next launch receives the earlier
launch's stored arrays through explicit allocation views. Completed execution
exists without numerical assumptions. Under the existing finite encoding,
range and strict ReLU-margin conditions, every completed admitted composition
has error bounds against TorchLean's generated backward for all three gradient
tensors. A margin means the real affine value is far enough from zero that
rounding cannot change its sign. Empty dimensions and spare pointwise lanes
are covered. These bounds do not assert bitwise agreement with PyTorch or GPU
hardware, and finite existence does not assert scheduler fairness.

Dense groups compute global addresses from logical row-and-column coordinates,
but shared addresses from their local column and reduction round. Their private
shared allocation contains exactly one row of fresh reduction planes. Reducing
this allocation must preserve actual fetched address checks, producer identity,
barrier ordering, admitted execution existence and universal output correctness.
