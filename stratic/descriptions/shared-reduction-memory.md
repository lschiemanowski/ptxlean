# Memory observations of the shared reduction

The reduction's memory graph contains the initial contents of both arenas and
all memory accesses emitted by its actual machine execution. An arena is one
selected region of storage: global storage holds the inputs and final output,
and shared storage holds the temporary words owned by this cooperating thread
array. Equal numeric offsets in the two arenas denote different words.

Each access retains its fetched instruction, issuing thread, selected arena,
computed byte address and value. Its position is the index in the complete
machine trace, before memory filtering. These positions include other threads'
steps and barrier events; restricting their order to one thread preserves that
thread's execution order. Repeated visits to a loop instruction remain distinct.
The graph combines both arenas, so an ordering path can pass through global and
shared accesses. It never proves each arena in isolation and then discards the
connections between them.

Read-source and write-order choices are parameters of this graph. They cannot
change the already executed trace. Initialization supplies the arbitrary fixed
initial words; it does not promise zero-filled storage. Source compatibility
requires every read to obtain its value from a write to the same represented
word. The reduction must derive its global input reads from initialization and
its shared reads from the corresponding producer stores, using proved facts
about actual execution and the completed barrier. Desired results, fresh shared
reads and unique producer stores are not supplied as unchecked premises.

Cross-barrier order is justified by actual same-key arrival and completion
events in the trace. The earlier access must precede its own thread’s arrival,
and the later access must follow completion after its own thread arrived.
Ordering is not inferred from a shared address or from a read-source choice.

Access-origin and completeness proofs ensure that no actual memory effect is
invented, dropped or duplicated. Byte alignment and storage bounds are separate
execution-safety obligations; dividing an address by four alone does not prove
them. A chronological witness orders writes by a finite rank and proves that
every read uses a matching preceding write with no later preceding competitor.
This is a sufficient construction for a selected execution, not a restriction
on the universal candidate theorem. A constructive completed execution additionally needs compatible read
sources, write ordering and a finite argument excluding circular justification
of computed values. These obligations remain distinct from the universal
correctness theorem and from whether the model faithfully represents PTX.

The specialization is one isolated CTA, ordinary generic proxy, aligned u32
words, relaxed GPU-scope global accesses and relaxed CTA-scope shared accesses,
one fully completed barrier phase and no external or asynchronous interference.
Its graph constraints are necessary conditions for this restricted candidate
execution model, not a complete acceptance criterion for arbitrary dependent
PTX programs. Ownership, valid launch geometry and correspondence of the
abstract barrier to the target remain explicit source-level conditions.
