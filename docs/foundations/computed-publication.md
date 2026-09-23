# Publishing a computed value

The earlier message-passing example writes a fixed payload. This example makes
the payload depend on real scalar instructions: two loads feed an addition, and
its result is stored from a register. It connects scalar computation to memory
ordering without pretending to solve arbitrary dependent concurrent programs.

## Follow the two threads

The shared arena contains four initialized 32-bit words. Their byte addresses
are offsets in this formal arena, not claims that a physical GPU application may
access absolute address zero. The first two words contain arbitrary inputs `x`
and `y`; the payload contains arbitrary `old`; the flag contains zero. The words
start at byte offsets 0, 4, 8 and 12. All register and predicate contents are
arbitrary initially. Each register that matters is explicitly written before use.

The producer's typed instruction encoding is:

```ptx
ld.relaxed.gpu.global.u32 r0, [0];
ld.relaxed.gpu.global.u32 r1, [4];
add.u32 r2, r0, r1;
st.relaxed.gpu.global.u32 [8], r2;
mov.b32 r3, 1;
st.release.gpu.global.u32 [12], r3;
exit;
```

The consumer executes:

```ptx
ld.acquire.gpu.global.u32 r0, [12];
ld.relaxed.gpu.global.u32 r1, [8];
exit;
```

These are illustrative instruction spellings; this project accepts typed operands,
not these raw strings or a complete PTX module. Register declarations, physical
allocation, argument passing and launch validation remain outside this example.

The consumer does not spin or branch. The theorem says that **if its flag
register is one, its payload register contains `x + y` modulo `2^32`**. It does
not promise that every run sees one. Both threads explicitly execute `exit`:
seven producer dispatches and three consumer dispatches suffice. This finite
existence result does not imply that a GPU scheduler will run either thread.

## Instruction order belongs to the fetched instruction

`Ptx/ComputedPublicationMachine.lean` defines the small `Scalar.Ordered` layer.
Its operation datatype contains move, addition, ordered load, ordered
register-source store, and exit. There is no unrestricted “scalar operation”
constructor through which an unqualified memory operation could enter.

`Instr.erase` reuses the existing scalar machine for local value computation,
register changes, predicates, address checks and stopping. Erasure drops only
the ordering information needed by the memory graph. It does **not** assert that
an acquire load is textually or concurrently equivalent to a relaxed load.
The ordered `encode` and `decode` retain the actual qualifiers and have a checked
round trip. Stores structurally require a register source; the decoder rejects
literal-source stores. This is a separate typed frontend from `Scalar.Text`,
whose existing memory forms remain relaxed.

`label` obtains the ordered instruction from the occurrence's actual program
counter. It checks that the scalar occurrence contains that instruction's
erasure, executed its guard, and emitted the matching kind of memory effect.
The value and byte address are the actual scalar effect's fields. Graphs store
word indices; `label_byte_address` recovers the exact byte address when it is
four-byte aligned. The position is the original dispatch index, so arithmetic,
move and skipped instructions leave gaps between memory positions.

Two directions are checked. `label_origin` proves that an emitted label has the
matching fetched instruction, qualifier and effect. `label_complete` proves
that every successful fetched memory step emits a label. `skipped_no_label`
proves that a false guard emits none. `events_origin` ties each event to the
actual run's dispatch index. The concrete `events_eq` theorem additionally
computes the entire table from both instruction runs:

| Event | Origin | Position | Memory action |
| --- | --- | --- | --- |
| 0 | initialization | 0 | input `x` at word 0 |
| 1 | initialization | 1 | input `y` at word 1 |
| 2 | initialization | 2 | payload `old` at word 2 |
| 3 | initialization | 3 | flag zero at word 3 |
| 4 | producer | 0 | relaxed input load, candidate `left` |
| 5 | producer | 1 | relaxed input load, candidate `right` |
| 6 | producer | 3 | relaxed payload store, actual `left + right` |
| 7 | producer | 5 | release flag store, actual one |
| 8 | consumer | 0 | acquire or relaxed flag load |
| 9 | consumer | 1 | relaxed payload load |

Candidate load values are proposed observations, not assumed permitted values.
Each local run has an arena used for bounds checking; its local memory list is
not a global scheduler interleaving. The graph connects threads through the
actual source of each read and the ordering of writes. In particular, the
consumer's initial local arena does not imply that its candidate reads must see
initial values.

## Why the result follows

`input_sources` first checks every possible write to the two input addresses.
Only initialization writes them. Thus a compatible graph forces the actual
producer load values to be `x` and `y`; its register computation and payload store
therefore contain their wrapping sum. This establishes the computed value,
rather than assuming the desired final equality.

If the consumer reads flag one, its source must be producer event 7: the only
other flag write initializes it to zero. The directly observed release/acquire
pair synchronizes. Producer program order, that synchronization, and consumer
program order create an ordering path from payload store 6 to payload read 9.
Their common address makes this a causality relation in the represented rules.
The payload read can obtain its value only from initialization or event 6.
Initialization precedes event 6 in write order, so the no-stale-read rule rejects
it as the source. The source must be event 6. This proof uses reusable
`Graph.direct_sync`, `publication_cause`, `source_of_initial_or_write` and
`value_of_source` lemmas.

`publication` quantifies over arbitrary read-source and write-order choices
satisfying `Graph.Valid`. `publication_observed` states the same fact using the
consumer's actual final register, and includes completion. It does not prove
correctness merely for the explicitly constructed successful graph.

## Existence, relaxed behavior and safety are different results

`success_valid` constructs a graph for every initial input pair. The input loads
read initialization, flag load 8 reads store 7, and payload load 9 reads store 6.
`successful_execution` supplies both actual local scalar derivations, their
halted outcomes and register results, graph validity and acyclic value grounding.
`producer_concrete` also identifies the producer run exactly with the ordinary
sequential arena interpreter once its input reads have their forced values.

`stale_valid` changes only the consumer flag order to relaxed and makes payload
load 9 read initialization. It still sees flag one. `relaxed_counterexample`
includes completed local executions and proves disagreement with the sum when
`old` differs from that sum. That inequality distinguishes the results; it is
not required for graph validity. Requiring acquire ordering excludes stale
sources even when the initial payload happens to equal the sum numerically.

`valueEdge` is explicitly this program's value-dependency graph: source edges,
plus the two input loads feeding the computed payload store. The flag value
comes from a literal move, addresses and control are fixed, and the consumer
never writes. Both witnesses give an increasing finite rank for these edges,
and therefore no cycle. This is supporting evidence about this program, **not**
a new proposed general no-thin-air rule. `input_sources` and `run_results` provide
the substantive grounding and computation equations independently of that graph.

`producer_safe` and `consumer_safe` apply to every candidate trace, even one
rejected later by the memory constraints. They establish byte alignment and
arena bounds through the existing scalar checks. `graph_memory_safe` checks the
same four-word bounds for every graph event. They do not establish allocation
ownership, physical pointer validity or runtime correctness.

## Source relationship and limits

All source anchors below refer to the checked-in PTX ISA 9.4 manual at
`references/nvidia/ptx-isa-9.4/index.html`, SHA256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.

- §9.7.10.8, `data-movement-and-conversion-instructions-ld`, specifies
  `ld.acquire.scope{.ss}.type` and `ld.relaxed.scope{.ss}.type`. Scope, relaxed and
  acquire qualifiers were introduced in PTX 6.0 and require `sm_70` or newer.
- §9.7.10.11, `data-movement-and-conversion-instructions-st`, specifies the
  corresponding release/relaxed store forms, with the same version and target
  requirements, and requires the stored operand to be in register state space.
  The wrapper uses `mov.b32` before storing the flag rather than inventing a
  supported literal-store text form.
- §8.8, `release-acquire-patterns`, and §8.9.4, `memory-synchronization`, support the
  directly observed release/acquire pair. §8.9.5, `causality-order`, separates
  transitive base paths from the final causality relation. The proof preserves
  that distinction; it does not add a transitive closure to `Graph.cause`.
- §8.10's coherence and causality constraints justify the existing necessary
  graph conditions. §8.10.4, `no-thin-air-axiom`, remains a broader semantic
  obligation. Adding register computation does not make `Graph.Valid` a complete
  admission criterion for arbitrary dependent PTX.

The wrapper does not itself validate a module's PTX version or target; use under
the documented source interpretation requires PTX 6.0+ and `sm_70`+. It models
one GPU, GPU scope, generic proxy, distinct aligned equal-size global words,
whole-word observations and initialized storage. There are no aliases,
mixed-size accesses, memory-mapped I/O, atomics, asynchronous effects, barriers,
floating point, other devices or general concurrency admission theorem.
Additional true PTX constraints could reduce the candidate executions; they
cannot invalidate the universal positive theorem proved from necessary rules.
The constructive graph/run witnesses are stated at the represented fragment's
boundary and make their noncircular computation explicit, without a hardware
conformance or general dependency-completeness claim.

To check the modules directly:

```sh
lake build Ptx.ComputedPublicationWitness
```

The release audit additionally prints theorem dependencies and rejects proof
placeholders and unapproved axioms. Lean checks the formal definitions and
proofs; independent comparison with the source establishes a separate kind of
evidence about whether those definitions faithfully describe the selected PTX.
