# Following the reduction's memory accesses

The machine trace records the executed instructions and collective-barrier events.
`Machine.Memory.access` recognizes a memory effect only when its thread matches,
the fetched instruction at the recorded block and program counter is exactly the
recorded memory instruction, its predicate enabled execution, and its load/store
direction matches the effect. The effect retains the actual byte address and word
value. This check is a structural adapter; actual-run completeness is proved
separately from the machine's step derivations.

`projection` numbers the full trace before filtering. A leader may visit the same
loop program counter many times. Those visits have different trace positions.
Other threads' instructions and collective events leave gaps in a given thread's
positions, which do not change its strict instruction order.

One graph includes both arenas. Global word `i` has graph address `2*i`, and shared
word `i` has graph address `2*i+1`. These numbers name logical words; they are not
GPU byte addresses. `spaces_distinct` proves equal numeric GPU offsets in different
arenas remain separate. `byte_recover` reconstructs the byte offset only with an
explicit four-byte alignment premise. The storage catalogue separately names the
global allocation and full device/grid/cluster/CTA identity of shared storage.
Bounds, ownership and launch geometry are not consequences of the address code.

`initial` enumerates every supplied initial global and shared word once, including
arbitrary old output and scratch values. `labels` appends precisely the per-thread
projections of the actual full trace. `labels_unique` proves distinct dynamic
identities for the combined list, including the disjoint initialization identities.
`graph` adds candidate read-source and coherence functions without changing labels.
`source_origin` derives that every read's selected source is either one of those
initial words or an actual projected store with the same address and word value.
It does not assume that the selected source is the newest store.

`run_access_complete` and `run_projection_complete` prove that every memory effect
emitted by an arbitrary actual run passes this adapter. `runGraph` fixes the
initial words to the actual incoming arenas. `run_global_input_read` then proves
that each global-input read's source is initialization and that its value equals
the supplied initial word, using Sources alone. The proof uses the actual fetched
output store's immediate address to exclude all program stores from input slots.

`barrierOrder` records actual same-key arrivals of both endpoint threads and an
actual completion between the memory accesses. `barrier_excludes_initial_source`
uses Ordered.Valid to rule out initialization for a same-address read after such
a store, even if the old and new words have identical bits. `barrier_unique_source`
exposes the additional unique-producer-store obligation; that helper does not
establish uniqueness by assumption for the concrete program.

`canonical_valid_exists` constructs compatible sources and coherence for the
actual complete canonical schedule. The source-reviewed `full_accesses` theorem
first derives the exact memory-access sequence from the executed producer,
barrier, loop and output steps. Every canonical global read uses initialization;
every shared read uses its matching producer store. A strictly increasing
phase/slot rank orders these real accesses, and a disjoint lower rank covers
initialization. The proof establishes injectivity, matching values, preceding
sources and absence of later competing writes, then discharges every
SerialCertificate field to obtain Ordered.Valid. Its separate `grounded` result
excludes cycles through actual memory base-order and read-source edges. The
certificate is a sufficient witness construction, not a restriction on the
universal arbitrary-candidate theorem or a complete PTX dependency model.

`run_shared_load_member_value` supplies the arbitrary-candidate read contract
used by the reduction's accumulator proof. Given an actual shared load at slot
`i < n` and Ordered.Valid for the combined execution graph, it derives that the
load returns the supplied input word. It imposes no restriction on schedules,
read overrides, initial scratch/output bits, or unused register seeds. The slot
bound and computed address remain structural loop obligations; the theorem does
not assume a final sum, source identity, uniqueness or a fresh observed value.

The argument has four independently checked parts:

1. `run_shared_write_slot` obtains each actual shared store's slot from the
   producer address invariant. `run_shared_write_unique` combines this with the
   actual per-thread publication count to exclude a second program write there.
2. `run_shared_store_before` uses a strict prefix of the chosen read's exact
   dynamic trace index. It locates the producer store and arrival, the reader's
   own arrival, and their actual same-key completion. At-most-one completion
   identifies the same dynamic completion position. Repeated PCs or identical
   event values are never assumed unique.
3. `run_shared_source` applies the barrier no-stale result and the proved unique
   store to force the read source. This remains valid when initial and stored
   bits happen to be equal.
4. The actual producer value invariant locates its earlier global load.
   `run_global_load_value` uses source compatibility to prove this load reads its
   initial input word. The shared result follows from that executed provenance.

The membership-facing result recovers an exact index from the actual trace; the
indexed theorem is also exposed. This lets the execution invariant discharge its
read contract without importing the memory model into the local interpreter.
Final accumulator/output reasoning and access safety compose with these memory
results in the reduction's top-level proof.

Ownership, scope, target eligibility, whole-word abstraction and the abstract
collective's correspondence to PTX remain distinct source-fidelity conditions.
The selected witness's base/RF acyclicity is a conservative memory grounding
argument, not a complete general PTX dependency semantics or hardware claim.
