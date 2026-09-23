# Byte-level observations

A read can combine bytes from different writes, producing a torn value. This
model records which write supplies each byte and checks whether the combination
is permitted. A memory event is the record of one read or write. Events here
access aligned four-byte words in global memory, using thread identities and scopes supplied by the execution environment.
Allocation and instruction-support checks are separate contracts. Partial overlaps between
different access sizes and additional memory-access mechanisms are excluded.

PTX's single-copy atomicity rule governs whether a read may mix bytes from
different writes; it applies only to qualifying pairs of operations. Accesses whose scopes exclude
one another are not forced to take the entire word from one write. Examples
construct permitted combinations and prove rejection when the applicable
ordering and atomicity conditions forbid them.

A whole-word description is justified when all bytes of a read choose one write
event, called uniform sources. Proofs distinguish conditions ensuring this from
the weaker fact that the byte values happen to agree. They state when the two
models have exactly the same valid candidates. General programs where reads
influence later writes still need a separate no-thin-air argument: values must
not be supported solely by circular justifications. An arbitrary ban on dependency
cycles is not substituted for that obligation.

The manual leaves a question about observation order, the relation connecting
qualifying source writes and reads for synchronization, when a read mixes sources.
The model exposes alternative interpretations. A result claimed independent of
that choice is proved under each; no convention is silently declared to be the
uniquely correct interpretation of PTX.

## Bytes, events, and ordering

Each event accesses an aligned four-byte unsigned value, abbreviated `u32`, in
the global memory arena, a list of four-byte words. Equal word addresses overlap completely; different word
addresses do not overlap. A source map records a write event for each of a read's
four byte offsets. Compatibility requires a write to the same word with the same
value for that byte. Numerically equal writes can still be different events.

The byte containing the lowest-value bits has offset zero, the lowest address.
This is little-endian layout; endianness names the order in which a value's bytes
are stored. The choice follows NVIDIA's supplemental application binary interface
(ABI) guidance about data representation, not a layout statement attributed to
the pinned PTX instruction-set manual's memory chapter.

Initialization represents the starting contents by one event for each word,
before later writes to that word. Each byte can independently select this event.
Program events come from traces, the records of local instruction execution.
Addresses and stored constants are fixed in the represented language. These
simplified stores do not assert that PTX text allows literal data operands for
stores; actual PTX store data comes from a register. Grouping initial bytes this
way does not justify mixed-size overlap, different addresses naming the same
storage (aliases), or arbitrary programs with register-dependent stores.

Communication links a write to a read if any byte selects that write. It links
a read to a write if any byte's source precedes that write in coherence, the
write ordering explained by the parent. Observation feeds synchronization and
causality. All these source-dependent relations are rebuilt from the byte map,
not borrowed from the first byte's source alone. Rules excluding causally future
sources or obsolete sources apply to each byte. Per-location consistency excludes
cycles combining same-address program order and morally strong communication.
Causality is not replaced by its transitive closure: an edge from A to B and one
from B to C do not automatically add A to C to that relation.

## Qualified atomicity and a small example

Coherence orders writes to the same word without requiring every pair to be
ordered. As explained by the parent, it is transitive and no write precedes
itself; these properties make it a strict partial order. Initialization comes
first. For the represented instructions using the generic access mechanism, moral strength requires two
non-initial accesses to the same word and either local program order or mutual
scope inclusion. If a read R is morally strong with write W and takes a byte
from W, single-copy atomicity forbids taking another byte from a write that precedes W in coherence
(a coherence predecessor). This does not unconditionally require one source: writes left unordered by coherence or writes outside the relevant scope need separate consideration.

Initialize a word to `0x00000000`; one CTA writes `0xffffffff`, and another CTA
on the same device reads. With CTA scopes, the read can take low-address bytes `00,00` from
initialization and high-address bytes `ff,ff` from the program write, yielding
`0xffff0000`. The example constructs local execution and verifies all represented
memory constraints, not just atomicity. Changing only the scopes to GPU forbids
that source assignment: the read and program write become morally strong, while
initialization is a coherence predecessor. Both results hold under either
observation policy. They are model results, not GPU measurements.

## The unresolved observation interpretation

The pinned manual's communication rule explicitly refers to any byte, whereas
its observation wording does not settle how to interpret a read mixing writes.
The model exposes two policies for observation from write W to read R:

- `anyByte`: at least one byte of R chooses W, and W and R are morally strong.
- `wholeSource`: every byte of R chooses W, and W and R are morally strong.

Both compare source identity, not just numerical equality. This choice can affect
synchronization and causality. Neither policy is asserted uniquely faithful to
PTX. The relaxed torn-read example has no synchronization and cannot distinguish
them. Determining the intended interpretation remains a semantic-fidelity
obligation even though the stated theorems are checked by Lean.

## When a whole-word model is justified

Uniformity means that every byte of each read chooses the same write event.
Under that condition, byte validity is equivalent to validity of the scoped
whole-word projection, obtained by selecting the first byte's source for the read. Conversely, repeating an existing whole-word source at
all offsets preserves validity. Both policies agree on uniform sources.

In a valid candidate, uniformity follows when the selected source writes are ordered one way or the other
in coherence for every distinct pair and the read is morally strong with each non-initial source.
Two different sources would have a later one, and atomicity against that write
would exclude the earlier one. Initialization's earliest position handles the
initial-source case without assigning initialization an issuing thread.
Mutual scope coverage of all non-initial events supplies the needed conditions:
byte validity is then exactly uniformity together with validity in the original
whole-word graph. This is a theorem under that scope restriction, not a new
atomic-read assumption. Equal byte values alone never establish uniformity.
