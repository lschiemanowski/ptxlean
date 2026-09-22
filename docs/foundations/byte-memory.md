# Reading a word from several writes

The byte model removes the earlier requirement that every byte of a read choose
the same write. It retains aligned, four-byte `u32` accesses, one generic proxy,
explicit scopes, and the normalized dependency-free program language. It proves
an admitted torn candidate, rejection when the relevant scopes enforce
single-copy atomicity, and an exact relationship to the previous whole-word model.

One source interpretation remains explicit: the pinned PTX manual does not spell
out how its observation-order phrase “reads the value written by” applies when a
read combines bytes from different writes. `ObservationPolicy` represents two
interpretations, `anyByte` and `wholeSource`. The specialization and examples are
proved for both. This does not establish which interpretation uniquely matches
PTX. See the [source review](next-source-review.md) for that precise remaining
semantic-fidelity obligation and the separate endianness source.

Start with [`Ptx/ByteMemory.lean`](../../Ptx/ByteMemory.lean), then inspect the
small actual programs in [`Ptx/ByteExamples.lean`](../../Ptx/ByteExamples.lean).
Lean checks the proofs against these definitions; the relationship between the
definitions and NVIDIA's documented semantics remains a distinct review question.

## A candidate at byte granularity

`ByteGraph` keeps event labels, coherence, topology, and scope, but its source map
has type `event → Fin 4 → event`. For each byte of each read, `Sources.compatible`
requires a write to the same word and equality of that byte's value. It does not
require equality of the entire read word with a selected write word.

Byte offset zero is the least significant byte. `wordByte` extracts eight bits
using division and reduction modulo 256. This is a selected little-endian ABI
convention: the [NVIDIA PTX interoperability guide][endian] describes current GPUs
as little endian. The project does not misattribute that statement to a passage
in the pinned ISA 9.4 HTML. `little_endian_example` checks that `0x44332211` has
increasing-address bytes `11,22,33,44` in hexadecimal. `word_eq_of_bytes` proves
that equality of all four bytes determines equality of the whole `u32` value.

Event addresses remain word indices. Byte offset `i` denotes byte address
`4*wordAddress+i`. All represented accesses cover the same four offsets. Two
accesses therefore either overlap completely or are disjoint. The model does not
support unaligned accesses, mixed-size partial overlaps, virtual aliases, or
alternative proxies. Those would require a richer footprint and address model.

Initialization remains the existing normalized write per initialized word,
before every later write to that word in coherence. Its four bytes can now be
selected independently. Program events still come from local execution:
`Program.byteGraph` decorates `Program.events` with byte-source choices; it does
not accept invented instruction traces. `Program.ByteAdmitted` requires arena
bounds, injective identities for the actual program threads, and all byte-model
constraints under the specified observation policy. Target eligibility and
allocation/access contracts are separate, as in the scoped foundation.

## What changes in the memory relations

The following rules are linked to the [pinned PTX source][source].

| Relation or constraint | Byte-model definition | Source |
| --- | --- | --- |
| Reads-from communication | A write precedes a read if at least one byte uses that write as its source. | [communication order][communication] |
| From-read communication | A read precedes a write if one of its byte sources precedes that write in coherence. | [communication order][communication] |
| Observation | Morally-strong qualification, together with the selected `anyByte` or `wholeSource` interpretation. | [observation order][observation] |
| Synchronization and causality | Recomputed from the byte observation relation, with the existing release/acquire patterns, base paths, and proxy restrictions. | [synchronization][sync], [causality order][cause] |
| Future-read exclusion | A read cannot source any byte from an overlapping causally later write. | [causality axiom][causality] |
| Stale-read exclusion | For every overlapping causally preceding write, each read byte excludes coherence predecessors of that write. | [causality axiom][causality] |
| Per-location consistency | Cycles are forbidden in overlapping program order plus morally-strong byte communication. | [SC per location][sc] |
| Single-copy atomicity | The qualified predecessor-source conflict described below is forbidden. | [atomicity][atomicity] |

The first-byte projection is useful for relating models, but the byte model never
reuses its source-dependent observation, communication, or causality relations.
In particular, `Coherent.justified` uses byte-derived causality. Coherence remains
partial when writes are unrelated by the applicable scope and causality rules.

`SingleCopy` follows the documented qualified rule. If read R and write W are
morally strong, and R reads any byte from W, R cannot read another byte from a
write W' that precedes W in coherence. This is not an unconditional equation
saying that all four source identities agree. Incomparable writes do not become
comparable merely because one read takes bytes from both. Initialization does
not acquire an issuing thread or become morally strong just to simplify a proof.

The selected fragment has no RMW or fence-SC operations. Its constant stores and
fixed instruction traces retain the earlier dependency-free restriction. The byte
extension does not solve no-thin-air admission for arbitrary register-dependent
concurrent kernels. In particular, it does not introduce a global communication
cycle prohibition as a substitute for that obligation.

## A genuinely torn result

The test program initializes one word to zero. One thread writes `0xffffffff`;
a different CTA's thread reads that word once. Both operations use CTA scope.
The example uses the normalized constant-store language, not a claim that PTX
`st` accepts an immediate data operand. A literal-source PTX listing would use a
register move before the store.

The read chooses the following sources:

| Byte offset | Source | Read byte |
| --- | --- | --- |
| 0 | Initial write `0x00000000` | `00` |
| 1 | Initial write `0x00000000` | `00` |
| 2 | Program write `0xffffffff` | `ff` |
| 3 | Program write `0xffffffff` | `ff` |

The resulting word is `0xffff0000`, distinct from both complete write values.
`torn_execution_exists` constructs this admitted candidate and its actual final
load-register result under each observation policy. `memory_safe` establishes
the one-word arena's alignment and bounds. The threads are in different CTAs on
the same device, so their CTA scopes do not mutually include one another.

Changing only the scopes to GPU makes the read and program write morally strong.
`in_scope_torn_forbidden` then applies `SingleCopy`: the high bytes come from the
program write, but the low bytes come from its coherence predecessor, the initial
write. This contradiction holds under either observation policy. The proof does
not infer rejection from an unsuccessful search or an absent witness.

These are facts about the represented memory constraints and actual local
traces. They are not measurements of a GPU or a hardware-conformance theorem.
Their validity under both policies does not resolve the observation wording:
these minimal relaxed tests do not depend on the disputed interpretation.

## Returning to the whole-word model

`ByteGraph.Uniform` requires every byte of a read to use its first byte's source
identity. Source entries for non-read events are irrelevant. Under this explicit
condition, `projection_valid_iff` proves equivalence between byte validity and
validity of the first-byte `ScopedGraph` projection. Full word-value equality is
recovered using `word_eq_of_bytes`; it is not assumed separately.

Conversely, `ofScoped` assigns an existing whole-word source to all four bytes.
`ofScoped_valid_iff` proves an exact embedding of the existing scoped whole-word
model for either observation policy. `uniform_policy_independent` proves the
policies agree on uniform-source graphs. Combined with the earlier scoped
`valid_legacy` theorem, this preserves the original all-in-scope fragment.

The projection is not valid without its premises. `torn_projection_invalid`
shows that the torn test cannot be admitted by the old whole-word interpretation:
its first byte selects initialization, whose complete value is zero rather than
`0xffff0000`.

`sources_uniform_at` provides a sufficient condition for deriving uniformity.
It requires pairwise coherence comparability of the chosen source writes and
moral strength between the read and each chosen non-initial write. Atomicity then
excludes any pair of distinct chosen sources. `coherence_later_not_initial`
handles initialization using its explicit earliest order, without treating it as
a morally-strong program access. The theorem does not assert that arbitrary
out-of-scope sources satisfy these premises.

For the original mutual-scope restriction, those premises follow from validity.
`uniform_of_all_in_scope` derives uniform sources using coherence totality for
non-initial writes and initialization's earliest order for initial sources.
`all_in_scope_valid_iff` consequently characterizes byte validity as uniform
sources together with validity of the unchanged legacy whole-word graph. Thus
the original fragment's scope restriction supplies uniformity; no additional
atomic-read assumption is needed. This conclusion holds for either observation
policy and does not extend to arbitrary out-of-scope accesses.

Finally, equal values do not establish uniform source identities.
`equal_value_not_uniform` uses initial and program writes that both contain zero:
the read is also zero, yet its bytes choose two distinct writes. The model and
specialization keep that distinction visible.

[source]: ../../references/nvidia/ptx-isa-9.4/index.html
[communication]: ../../references/nvidia/ptx-isa-9.4/index.html#communication-order
[observation]: ../../references/nvidia/ptx-isa-9.4/index.html#observation-order
[sync]: ../../references/nvidia/ptx-isa-9.4/index.html#memory-synchronization
[cause]: ../../references/nvidia/ptx-isa-9.4/index.html#causality-order
[causality]: ../../references/nvidia/ptx-isa-9.4/index.html#causality-axiom
[sc]: ../../references/nvidia/ptx-isa-9.4/index.html#sc-per-loc-axiom
[atomicity]: ../../references/nvidia/ptx-isa-9.4/index.html#atomicity-axiom
[endian]: https://docs.nvidia.com/cuda/archive/12.8.0/ptx-writers-guide-to-interoperability/index.html#bit-fields
