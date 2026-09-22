# Source review: byte observations and shared-allocation kernels

This review uses the [pinned PTX ISA 9.4 source](../../references/nvidia/ptx-isa-9.4/README.md).
It separates a faithful transcription of the stated constraints from choices
that need a further correspondence argument. The [earlier review](blocks12-source-review.md)
explains the unresolved dependent no-thin-air problem; introducing byte sources
does not solve it.

## Byte sources, values, and initialization

[Memory operations][operations] act on bytes. For this extension, each event
still accesses one aligned four-byte word; different word indices are disjoint,
and matching indices overlap completely. There are no mixed-width accesses,
aliases, additional proxies, vector accesses, atomics, or asynchronous accesses.
Consequently, a read source can be selected separately for each `Fin 4` byte
offset while retaining the existing operation-level program order and coherence.
Source compatibility must check the source is a write to the same word and that
the particular byte value agrees. Equal byte values do not identify equal
source events.

Increasing byte offsets use little-endian decomposition. This is an explicit
representation choice supported by the separate NVIDIA
[PTX Interoperability 12.8 ABI guide, §2.3][endian]. The pinned ISA's memory-model
chapter specifies byte locations but does not itself state that layout rule.
The ABI guide is supplemental provenance, not a passage of the pinned ISA.

[Initialization][initialization] gives each byte an initial write before program
threads begin. The representation groups the four initial bytes of each word
into one event with their supplied values. Selecting that event independently
at different offsets can still express a mixture of initial and later bytes.
This relies on fixed complete overlap, one initial event per word, and an
initial-before-program-write coherence rule. It is not a justification for
reusing the grouping in mixed-width or aliased storage.

## Atomicity does not unconditionally mean one source

For a morally strong read/write pair `R,W`, [single-copy atomicity][atomicity]
forbids selecting a byte from `W` and another byte from a write preceding `W` in
coherence. This is the constraint to encode. It does not say that every read
must select all four bytes from one event. In particular, scopes that exclude
each other do not establish this read/write guarantee, and coherence itself is
partial for racy writes.

A sufficient route to uniform sources is stronger and should be stated as a
theorem with explicit premises: distinct selected source writes are comparable
in coherence, and each noninitial source write is morally strong with the read.
Any two distinct sources would then contain a later write; initialization-first
ensures that later write is noninitial. Atomicity against the later write
excludes the earlier source. Uniform source identity implies uniform source
value, but the converse need not hold when different writes contain equal
bytes. This argument is a sufficient condition, not an unconditional
normalization of arbitrary scoped PTX executions.

A useful discriminating example initializes a word to `0x00000000`, writes
`0xffffffff` in another CTA, and reads `0xffff0000`, choosing two bytes from
each source. CTA-scoped operations outside each other's scopes can leave this
candidate admissible under the represented constraints. Making the store and
read mutually GPU-scoped forbids it: the initial write precedes the program
write, so the read violates the qualified atomicity clause. An example should
check the entire candidate, not only this one axiom.

## Relations that must be rebuilt from byte observations

| Relation or constraint | Fixed-width byte interpretation |
| --- | --- |
| [Communication][communication], write to read | Some byte selects that write as its source. |
| Communication, read to write | Some read byte selects a write preceding the target write in coherence. The shared-byte side condition follows from complete overlap and source/coherence typing. |
| Communication, write to write | The chosen operation-level coherence relation. |
| [Coherence][coherence] | A strict transitive partial order; comparable for overlapping morally strong or causally related writes; racy noninitial writes remain unrelated. |
| [Causality][causality], no future read | A read causally before a write cannot select that write at any byte. |
| Causality, no stale read | For each byte, a read causally after a write cannot select a coherence predecessor of that write. |
| [SC per location][sc] | Acyclic overlapping program order together with morally strong communication, now using the byte-derived communication relation. Cross-location program order is not inserted into this axiom. |

The event's old whole-word source field must not accidentally supply these
relations. In particular, synchronization, base causality, final causality,
coherence justification, and the per-byte causality checks must all use the new
observation construction. The final causality relation still must not be
transitively closed.

There is a narrower fidelity question at [observation order][observation]. That
clause describes a morally strong read receiving the value of a write; unlike
communication, it does not explicitly say whether one sourced byte suffices
when a read mixes sources. This review does not establish a unique
interpretation for torn synchronization from that wording. `ObservationPolicy`
therefore exposes `anyByte` and `wholeSource`; agreement on uniform sources
isolates this issue from the earlier model. Tests containing only relaxed
operations and no synchronization do
not settle it. Neither a checker theorem nor a choice of policy should be
reported as resolving NVIDIA's intended rule for such torn observations.

The atomicity clause alone does not remove this question: a read can be morally
strong with one source write while another source write is outside its scope
and incomparable with the first in coherence. The forbidden predecessor pair
need not occur in that case.

A whole-word specialization must preserve the actual source event at every
offset, establish byte-value compatibility, and show equality of the derived
relations. It must include the atomicity obligation, which follows for uniform
sources from coherence irreflexivity. This is an equivalence on the uniform
subclass, separate from proving that a broader byte execution is uniform.

## Shared-allocation vector addition

The intended vector-add proof can use read-only input words and one distinct
output word per lane in a single allocation. The trace must come from actual
load, load, register add, register store, and exit steps. Inputs and outputs are
disjoint; inputs have no program writes; output ownership is injective. Byte
addresses, alignment, bounds, pointer non-wrapping, initial values, and the
mapping from lane identities to distinct program threads are separate contracts.
All memory operations are strong, GPU-scoped, global, and generic-proxy on one
device. Constant per-lane addresses exclude dynamic address dependence here.

These conditions give two useful arguments. Operationally, other lanes cannot
modify a lane's inputs or its output, so instruction-level interleavings
preserve its local arithmetic result. Relationally, every input byte has only
its matching initial write as a compatible source. The load value is therefore
grounded independently of the later register-dependent store; the addition
computes modulo `2^32`. Outputs are not read back, so their stores cannot
self-justify any of the input values. This is a concrete acyclic grounding
argument for this kernel, not a new general no-thin-air axiom.

An explicit finite schedule establishes execution existence for the supported
machine and a trace-labelled graph satisfying the represented relational
constraints. Universal results over that interleaving machine do not, by
themselves, quantify over all PTX executions. A universal relational result
must separately state its candidate-trace and source premises. Neither result
establishes GPU scheduling fairness, hardware progress, compiler preservation,
or a full launch/module ABI.

[operations]: ../../references/nvidia/ptx-isa-9.4/index.html#memory-operations
[initialization]: ../../references/nvidia/ptx-isa-9.4/index.html#initialization
[atomicity]: ../../references/nvidia/ptx-isa-9.4/index.html#atomicity-axiom
[communication]: ../../references/nvidia/ptx-isa-9.4/index.html#communication-order
[coherence]: ../../references/nvidia/ptx-isa-9.4/index.html#coherence-order
[causality]: ../../references/nvidia/ptx-isa-9.4/index.html#causality-axiom
[sc]: ../../references/nvidia/ptx-isa-9.4/index.html#sc-per-loc-axiom
[observation]: ../../references/nvidia/ptx-isa-9.4/index.html#observation-order
[endian]: https://docs.nvidia.com/cuda/archive/12.8.0/ptx-writers-guide-to-interoperability/index.html#bit-fields
