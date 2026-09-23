# Independent proof review of affine memory observations

The reviewed `Ptx/AffineMemory.lean` has no identified proof or hidden-premise
blocker. Source SHA-256:
`9eedf656d425a7e3fb4f72d1fff7d739752d5cbf1168133df9768c07a7d5d172`.
This reviews the prescribed memory graph, not a fetched arithmetic program or
hardware behavior.

The graph has one initialization per arena location and exactly three reads
followed by one store from thread zero. The four program-event indices are
distinct; the occurrence positions are 0, 1, 2 and 5. The default branch of
`programEvent` cannot create extra graph events because the graph index type
restricts its argument to these four slots. Input/output addresses can coincide
without creating duplicate initialization writes.

`valid_reads_initial` permits arbitrary candidate read values, store value,
source function and coherence relation. It does not assume the reads select
initialization. `Sources.compatible` excludes read events as sources. If a read
selects the sole program store, compatibility supplies the same-address fact,
and read-before-store program order supplies the existing unclosed causality
relation. `Valid.no_future` excludes that source. The remaining initialization
must have the input address, so compatibility derives its initial word value.
This argument retains every full-word alias pattern, including all four
arguments aliasing and stored bits equal to or different from initial bits.

`witness_valid` discharges the entire `Graph.Certificate`: source compatibility,
all five coherence obligations, base-edge inclusion/transitivity/irreflexivity,
coherence versus causality, no-future/no-stale, and the per-location edge rank.
No graph-validity field or expected read premise is omitted. Its auxiliary
`upper` bounds program-order paths; it is not substituted for the actual memory
semantics. Initialization-sourced reads have no morally strong observation edge,
which justifies simplifying that part of the witness certificate. The coherence
order contains only output initialization before the final store, sufficient
because those are the only distinct writes sharing an address.

The witness exists for arbitrary supplied stored bits and all well-typed input
and output indices. The concrete one-word all-alias example establishes a
nonempty instance. It does not prove those stored bits are an arithmetic result.
The separate grounding rank covers this witness's program-order/read-source
union, including initialization-to-read edges. Its acyclicity theorem is a
proved property of this particular graph, not an extra rule imposed on all PTX
executions or a general no-thin-air result.

`wordIndex` requires the existing `ValidAddress`: the supplied 64-bit byte offset
is divisible by four and its word quotient is within the arena. `wordIndex_bytes`
uses the zero remainder to recover the exact byte offset, without wrapping a
new pointer or silently rounding down an invalid address. `witnessAt_valid`
therefore preserves the caller's checked addresses. This is arena-relative
alignment/bounds, not allocation ownership, runtime pointer translation, byte
alias adequacy or safety against external accesses.

Independent fresh `lake env lean Ptx/AffineMemory.lean` elaboration passed.
A separate import driver printed dependencies for all 30 public endpoints in
[the module audit](affine-memory-audit.txt); exact-count validation accepted only
`propext`, `Classical.choice` and `Quot.sound`. The source guard found no omitted
proof, new axiom or `native_decide`. Independent logs are
`/tmp/ptx-affine-memory-independent-fresh.log` and
`/tmp/ptx-affine-memory-independent-audit.log`.

The declared PTX reading remains the isolated, aligned, whole-word relaxed
GPU/global fragment with one thread and its existing initialization normalization.
Actual mixed-trace event correspondence, arithmetic value grounding and numerical
correctness are separate obligations, accurately retained in the description and
[study guide](affine-memory-observations.md).
