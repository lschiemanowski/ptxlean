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

For an instruction list without jumps or scalar exits, each thread's recorded
instruction positions increase strictly, including its barrier arrivals and
final exit. A skipped instruction still advances its position. A waiting or
halted thread cannot emit another instruction event, and barrier completion
advances every participant past that barrier. Thus a thread cannot execute the
same store site twice. These facts concern arbitrary candidate reads and
permitted arithmetic results, without assuming that a read is fresh or that the
whole execution finishes. They establish control order; the kernel must still
connect each store's computed address to its owner.
For each observed completion, earlier thread events have instruction positions
at or before its barrier site, and later events have positions beyond it.
A barrier site cannot complete twice in such a program. These results turn
producer and consumer instruction positions into the timing facts required by
the visibility rule. The existence of the required phase and the identity of
its unique writer still need to be proved for the concrete kernel.

Address calculations can be proved separately from tensor values. A projection
keeps a chosen set of integer registers, all address registers and one active-lane
predicate. It omits tensor registers and floating-point results. Before using it,
every instruction in the program must be checked: a retained value may depend
only on retained inputs, and a tensor load or floating-point instruction may not
overwrite one. Agreement with this calculation is preserved by actual thread
steps, skipped instructions and barrier release. An emitted store then has the
address calculated by its thread's instruction prefix; an emitted store guarded
by the retained predicate also proves that predicate true. This is a proof aid
for the existing machine, not an alternate execution or memory rule. The current
projection retains the register set used by the dense kernel; other layouts need
their own compatibility check or a generalized projection.

A finished thread must have emitted an actual exit. For an instruction list
without jumps or scalar exits, moving past an earlier instruction cannot skip
it: ordinary steps advance by one, and only a completed barrier can move all
participants past a synchronization site. Crossing a memory instruction yields
its actual scalar evaluation and trace occurrence. A false predicate can still
skip that instruction, so a producer-existence proof must separately establish
that the store's predicate is true. These facts recover required events from
execution, without assuming successful scheduling of an unfinished run.

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
this alone does not make the resulting memory graph admissible. A concrete-read
execution additionally retains that each load used the current array rather than
a freely proposed word. This restriction applies only to an existence witness;
the general candidate relation and permitted floating-point results stay unchanged.
Replaying the recorded loads and stores must reproduce the arrays, including
the value observed by each load. This supplies evidence for constructing read
sources: every load must use the initial word when there is no preceding store,
or the value of the last preceding store to that location in the trace. Global
and shared locations are tracked separately. This does not itself discharge the
memory constraints. A selected concrete-read trace can supply a chronological
certificate: initial writes precede program events, each load uses its last
preceding write, and writes to the same location follow their trace order.
The certificate must also respect the ordering derived from actual barrier
arrivals and completions. Graph entries are grouped by thread, so their list
indices are not a global chronology. Each program event instead keeps its
position in the full instruction trace, including non-memory events; initial
writes occupy a separate earlier range. A proved source function selects a
compatible initial or last program write for every read. This is a mathematical
existence construction, not an executable graph-extraction tool. Its proof
establishes the existing restricted memory constraints and excludes circular
chains through order and read-source edges. It does not impose this selected
chronology on all permitted executions or establish general PTX semantics.

A two-thread witness supplies that additional proof: threads publish inputs, synchronize,
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
