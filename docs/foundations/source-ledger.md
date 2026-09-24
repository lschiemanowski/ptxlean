# Source correspondence for the scalar fragment

The normative input is the locally [pinned PTX ISA 9.4 manual](../../references/nvidia/ptx-isa-9.4/README.md),
SHA-256 `0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
The manual is acquired separately into the ignored local source cache. Links
below open NVIDIA’s website for reading; the committed hash and locators identify
the exact reviewed bytes used by source checks. This ledger is a reviewed
interpretation of prose; Lean does not prove the prose has been faithfully
translated. No hardware testing or comparison to another full PTX model is
claimed.

## Clauses and implementation

| Source clause | Lean responsibility | Interpretation within the restriction |
| --- | --- | --- |
| [ld](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#data-movement-and-conversion-instructions-ld), [st](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#data-movement-and-conversion-instructions-st) | `Instr`, `Instr.step`, `Step`, `Runs` | Only scalar global u32 relaxed/acquire loads and relaxed/release normalized literal stores, all GPU-scoped. Actual PTX stores take register sources; explicit constant-setting moves are folded into the memory-only representation, without a proved lowering theorem. PTX 9.4 and eligible sm_70-or-later target assumed. No parser, target-feature validator, launch semantics, or hardware execution. |
| [Initialization](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#initialization) | `Program.events`, `initial_origin`, `Coherent.initFirst` | Group four initial bytes into a word event, initialize every arena word exactly once, give it no ordinary issuing thread, and put it before other writes to that word in coherence. See normalization argument below. |
| [Morally strong operations](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#morally-strong-operations) | `morallyStrong`, `word_footprints_disjoint` | The strong GPU/generic accesses on one GPU are mutually in scope; same word means exact overlap. Initialization is handled separately. Distinct word indices denote disjoint aligned four-byte footprints. |
| [Release/acquire patterns](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#release-acquire-patterns) | `releasePattern`, `acquirePattern` | Direct qualified access, or applicable pair of same-address program accesses. Fence forms and RMW forms are unavailable in the syntax. Pair forms remain present even though the publication proof uses direct forms. |
| [Program order](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#program-order) | `po` | Strict occurrence order within one actual program thread. The global list index does not order different threads. |
| [Observation order](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#observation-order) | `rf`, `observation` | Source write to morally strong read. RMW chains are absent. Read-source compatibility additionally enforces same word and exact value. |
| [Synchronization](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#memory-synchronization) | `sync` | Different threads; release/acquire patterns; observation between relevant operations; morally strong pattern endpoints. Reading a release with a relaxed load alone is insufficient. |
| [Causality order](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#causality-order) | `base`, `proxyBase`, `cause` | Base is transitive closure of PO and synchronization. Generic proxy with identity addressing preserves same-address base endpoints. Causality is preserved base or one observation edge followed by preserved base, with no extra transitive closure. |
| [Coherence order](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#coherence-order) | `Coherent` | Strict transitive same-word write order, total among writes to a word; initialization first. No ordering is demanded across words. |
| [Communication order](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#communication-order) | `communication` | Read-from, coherence, and from-read (read's source is coherence-before the later write). |
| [Coherence axiom](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#coherence-axiom) | `Valid.coherence_cause` | Same-word writes ordered by causality must be ordered by coherence. |
| [Fence-SC axiom](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#fence-sc-axiom) | No fence constructor | No applicable instances, rather than an arbitrary assumed fence order. |
| [Atomicity axiom](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#atomicity-axiom) | `byteSource`, `single_copy`, `no_source_coherence_predecessor` | One complete word source per read provides uniform byte source; strict coherence excludes its preceding itself. No RMW operations. This encodes the matching-access restriction; it does not prove general byte-model normalization. |
| [No-thin-air axiom](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#no-thin-air-axiom) | Literal `Instr.store`, `store_origin`, `no_invented_values` | Store values, addresses, and execution are independent of loads. Every source is an actual initial/store event. The manual permits dependency-free cyclic communication patterns; no global RF+PO acyclicity is added. Value grounding alone would be inadequate once dependent instructions are introduced. |
| [SC-per-location axiom](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#sc-per-loc-axiom) | `locationEdge`, `Valid.sc_per_location` | Acyclic union of overlapping PO and morally strong communication. Cross-location PO is deliberately excluded from this union. |
| [Causality axiom](https://docs.nvidia.com/cuda/parallel-thread-execution/index.html#causality-axiom) | `Valid.no_future`, `Valid.no_stale` | Both bullets: a read cannot take a causally later write as source; a read cannot take a coherence predecessor of a causally earlier write as source. The second supplies publication. |

`Valid.base_irrefl` expresses that base causality is an order. It is a separate
well-formedness requirement, not an invented seventh §8.10 axiom. The six
§8.10 rules above are either implemented as constraints or accounted for by the
explicit instruction/word-source restrictions.

## Two points requiring care

The detailed §8.9.5 definition governs `cause`. A footnote in §8.8 informally
refers to transitivity of causality; that wording is not used to add a closure
beyond §8.9.5. In particular, the publication proof first constructs a base path
across two locations and then establishes same-address endpoints A and D.

The manual specifies initial writes at byte granularity. Here each entire arena
word has an initial bitvector, and all accesses match one entire word. Grouping
its four initial bytes preserves the values and initial-before-write order used
by this fragment. Initial events have no thread and cannot receive program-order
or synchronization edges. The implementation excludes initialization from
`morallyStrong`/observation and the filtered communication part of the
per-location check. Initial events have no incoming communication: no read
source has a coherence predecessor before initialization. Adding their outgoing
communication edges therefore cannot create a per-location cycle. Adding an
initial-write observation followed by same-word base order would impose only
already-satisfied initial-before-write/no-predecessor constraints. This is a
source-level normalization argument, not a checked equivalence to an independent
byte semantics. It must be revisited for mixed-size, overlapping, or aliased
accesses.

## Evidence and its limits

The independent semantic review checked the study and these relation choices
against the frozen source, including pattern endpoints, both causality bullets,
initialization, and the relaxed witness. Independent proof review checks the
Lean statements and their dependencies. These are different kinds of evidence.

The Lean results establish universal publication and explicit admitted successful
and relaxed executions; source compatibility and arena safety are actual
checked predicates, not assumed final outcomes. The successful witness prevents
vacuity of the acquire theorem. The relaxed witness guards against accidentally
imposing global sequential consistency. The register-result projection guards
against proving only a disconnected event-table fact.

The coverage claim is restricted scalar u32 message passing and its reusable
local/relational definitions. There is no complete PTX byte model, dependency
model, target validator, undefined-behavior semantics, hardware conformance
proof, compiler correctness proof, or GPU scheduling/progress theorem.

## Finite checking and litmus evidence

The [finite-checking guide](finite-checking.md) adds algorithmic and example
evidence without changing these semantic clauses. `Graph.check_iff` proves exact
equivalence to the existing validity predicate. The complete message-passing
outcome classification and the store-buffering, same-location, release-pair, and
acquire-pair results are checked relative to it. Independent source review
confirmed the intended behaviors against the pinned clauses; this does not
upgrade the source-level normalization argument to a checked PTX equivalence.
