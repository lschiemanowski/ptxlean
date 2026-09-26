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

The row-distributed dense program also has a universal forward theorem: whenever
its actual combined execution completes and satisfies its memory constraints,
its stored outputs have the prescribed arithmetic meaning and TorchLean error
bound. Its proof derives the input reads, each scratch producer, actual barrier
ordering and unique output writers from that same trace. A construction of a
completed admitted grid reduction is still missing, so this conditional theorem
is not yet a complete launch contract. Software interpreter examples do not
supply that missing proof. The multi-group backward composition is also unfinished.
