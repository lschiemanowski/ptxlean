# Changing graph names without changing memory constraints

A memory graph uses finite event IDs to connect reads to their supplying writes
and to record write order. The IDs are references, not the dynamic instruction
positions that determine program order. When assembling one graph from traces,
it is useful to renumber these references or encode storage locations using a
new set of natural-number addresses. `Ptx.GraphTransport` proves when these
changes preserve exactly the same existing constraints.

`IndexEquiv n m` provides a map from each new event ID to its old ID, an inverse
map and both inverse proofs. Thus no event can be dropped, duplicated or created.
This small structure uses the root project's existing Lean dependencies.
`transport g indices rename` maps every event label through the index map and
changes only its storage-address field. It retains the original thread,
dynamic position, operation kind and value. It maps a read source back into the
new event IDs and transports coherence by both old endpoints. Initialization
labels receive the same address renaming as program labels.

An injective address function never identifies two previously distinct storage
locations. Under that condition, `sameAddress` is an equivalence between new
and old address equality. Numeric address order is irrelevant to these graph
constraints; this theorem does not preserve physical pointer arithmetic,
alignment, byte extents or ownership. A concrete address translation must prove
its separate access and source-fidelity conditions. A noninjective renaming is
not covered by the validity theorem.

The module proves correspondence of read/write classification, acquire/release
patterns, read sources, observation, synchronization, base paths, the original
unclosed causality relation and per-location paths. Existential intermediate
events are carried using the inverse index map; nonempty paths are transported
in both directions. In particular, causality is not silently replaced by its
transitive closure.

`valid_iff` preserves and reflects every field of `Graph.Valid`: source
compatibility, coherence typing/order/initialization, base acyclicity, the
coherence/causality condition, no-future/no-stale conditions and per-location
acyclicity. Reflection matters: renumbering cannot make an invalid candidate
valid. The proof expands exactly the existing validity fields, so it adds no
semantic premise about desired outputs.

For `Graph.Ordered.Valid`, `order indices extra` transports precisely the existing
additional base-order relation. `ordered_valid_iff` proves the same two-way
validity correspondence. It neither invents synchronization edges nor proves
that supplied edges arise from an executed barrier; execution/source evidence
for the original extra order remains necessary.

Convenient special cases are `renameAddresses_valid_iff` and
`renameAddresses_ordered_valid_iff` for an unchanged event numbering, and
`reindex_valid_iff` and `reindex_ordered_valid_iff` for unchanged addresses.
The combined transformation can also be used directly. This is transport of
already defined memory constraints, not an admission theorem for arbitrary PTX
executions, a multi-space interpreter, or a proof of general no-thin-air behavior.

## Verification

Source SHA-256: `5edbbae37f8049987c90c09f70fa940136f01836cf84657f4144ffc14fd9dfac`.

```
lake --no-cache build Ptx.GraphTransport
lake --no-cache env lean Ptx/GraphTransport.lean
```

The targeted build and fresh source elaboration passed without warnings.
All 53 explicit public declarations, including 45 theorems, were enumerated and
freshly audited with `#print axioms`. The existing exact-name auditor accepted
only standard Lean axioms; this module's closure reports `propext` and
`Quot.sound`, with no new unchecked axioms. The forbidden-token source scanner
passed. Complete reports are in
[graph-transport-audit.txt](graph-transport-audit.txt).
