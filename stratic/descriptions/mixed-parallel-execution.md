# Cooperating integer and floating-point threads

A cooperating thread array (CTA) is a group of threads that can share a small
memory region and wait for each other at a barrier. This execution layer lets
threads fetch integer, binary32 and barrier instructions from one common
instruction list. Binary32 is the usual 32-bit floating-point format. Each thread
keeps its own registers, predicates and program counter, which identifies its
next instruction. A schedule chooses one thread to take the next step; no
simultaneous or lockstep hardware execution is assumed.

Several consecutive instructions can be proved together as a segment. Such a
proof checks that each instruction advances its thread and leaves the barrier
unchanged. Before using the segment in a program execution, its instructions
must match the common program at that thread's current position, and the thread
must be live and not waiting at a barrier. This allows short instruction proofs
to compose without replacing instruction execution by an assumed result.

There are two separate lists of memory words: global storage and the group's
shared storage. A memory instruction explicitly selects one of them. The tag
also remains on its trace event, so an access cannot silently change its memory
space. Every emitted access is four-byte aligned and within the selected list;
stores preserve both list lengths. Those facts hold even for a finite execution
prefix that later faults. They do not establish allocation permissions,
initialization, or successful program completion.

A load may use a proposed value. This makes it possible to describe candidate
executions before asking whether PTX's memory rules permit them. A successful
load's address check does not justify its value. The memory graph records every
successful access at its actual position in the execution. Initial contents are
separate writes with no issuing thread. Global and shared locations remain
distinct even when they have the same numeric address. The selected forms are
explicitly relaxed accesses at GPU scope for global storage and CTA scope for
shared storage; the generic word graph represents their common in-scope fragment.

A full-group barrier uses resource zero, a named synchronization slot, repeatedly.
Each completed use advances a generation number so that separate uses are not
confused. The first arrival records the instruction site. Waiting threads cannot
fetch another instruction, and later arrivals must match the site and resource.
Completion requires all participants. From a reset barrier, every execution
preserves the invariant that waiting threads remain at the recorded site; hence
release advances all participants from the same instruction. A finite schedule
witness fetches and completes two successive barriers at different sites using
the same resource and successive generations. It proves existence of that
control execution, not scheduler fairness or memory visibility.

Each recorded barrier completion is justified by earlier, actually emitted
arrivals from every participant, with the same CTA, resource, generation and
instruction site. This history property survives arbitrary scheduling and
resource reuse. A memory-ordering certificate uses those arrival positions and
the completion position; it cannot introduce a completion that the machine did
not execute. Memory labels retain their actual address, value, thread and
position. Connecting the certificate to memory constraints is separate from
proving a concrete kernel's write ownership and scratch-storage lifetimes.

If a location has exactly one program writer, that writer stores before its
arrival, and a consumer loads after the completed barrier, the memory constraints
force the consumer to read that writer. Initialization cannot supply a stale
value. The unique-writer condition includes the entire execution: a later
overwrite would violate it. Fresh scratch for each round makes this a useful
rule for reductions, but a kernel must still prove ownership and timing.

A selected software runner reads the current arrays and chooses the checked
binary32 reference result. Its steps are proved to be candidate-machine steps;
this alone does not make the resulting memory graph admissible. A two-thread
witness supplies that additional proof: threads publish inputs, synchronize,
compute sums, publish to fresh locations, synchronize again and store the peer's
result to separate outputs. It works for arbitrary input words, reaches exit in
both threads, and satisfies the original memory constraints. A chronological
certificate also excludes circular dependence through read sources. This is an
existence example, not a restriction on all candidate executions or a full layer
implementation.

The represented barrier discipline requires full participation without early
thread exits. General barriers with explicit participant counts, divergent
barriers, other resources, asynchronous barriers and multiple CTAs interacting
are outside this layer. Initial registers and memory are supplied explicitly.
The selected numerical target check is PTX 9.4 with sm_70 or newer; full GPU
launch limits, register declarations, PTX text parsing and runtime calling
conventions remain separate obligations. Fault and rejected-barrier outcomes
are interpreter results, not assertions about hardware traps.
