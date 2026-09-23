# Memory observations and ordering

When several threads use memory, it is not enough to say that their addresses
are valid. We must also say which writes a read may observe and how coordination
between threads constrains those choices. This responsibility supplies those
rules. It uses the execution environment's thread identities and scopes, while
memory-access permission and instruction support remain separate requirements.

A memory event records one read or write. A candidate memory graph collects
events, proposes which writes supply reads, and records required orderings.
Its validity means that these choices satisfy the represented memory rules.
Connecting the events to actual instruction execution is a separate part of a
kernel proof; a valid graph alone does not establish that a program produced it.

The current models cover aligned four-byte values, called words, in global
memory. Alignment means that each starting address is divisible by four.
Program addresses and stored values are fixed in the restricted language.
The simplified stores use literal constants internally; legal PTX stores instead
obtain their data from registers. General programs whose reads determine later
stores, addresses or branches need further justification, including exclusion
of values supported solely by circular dependencies.

## What thread scope contributes

An operation's scope identifies the participants it includes. CTA scope includes
its cooperative thread array, a group of threads that can share storage and
synchronize; GPU scope includes threads on the same device. Mutual scope inclusion
means each operation includes the other operation's thread. Cluster scope covers a group of CTAs within one grid, the collection launched
together. System scope covers the represented GPU threads of the host program,
the CPU program launching the work; CPU thread execution itself is not modeled. Scope controls which ordering guarantees
apply; it does not grant permission to access storage.

This model uses four-byte accesses and the generic proxy, PTX's term for the
memory-access mechanism used by these ordinary loads and stores. Other access
mechanisms and accesses of differing sizes are outside this fragment. For these
instructions, PTX calls a pair morally strong when they access the same word
and either occur in the same thread's instruction order or mutually include each
other in scope. Initial writes, which represent memory's starting contents,
have no issuing thread and are excluded from this qualification. Moral strength
determines which ordering and atomicity rules apply; atomicity here concerns
restrictions on combining bytes from different writes in one read.

Release and acquire are writer and reader ordering options. Qualifying patterns
of these instructions can establish synchronization, an ordering connection
between threads. Observation connects a qualifying source write to the read
that observes it. The resulting causality relation expresses the constraints
built from instruction order, observations and synchronization; its exact
construction must preserve the restrictions of the represented PTX rules.

Coherence is an ordering of writes to the same word. A write cannot precede itself;
if one write precedes a second and the second precedes a third, the first precedes
the third. Some pairs may remain unordered. Morally strong writes must be ordered
one way or the other, and initial writes come first. The order must also respect
causality, the ordering constraints derived from instruction order, observations,
and synchronization. Unrelated competing writes cannot be arbitrarily ordered
to make a proposed execution pass the checks.

## Whole-word and byte-level representations

Whole-word observations choose one source write for each entire read. This is a
simple representation when every byte of a read comes from the same write. If
that condition is not established, it describes only the outcomes with a single
source and can omit other permitted results.

Byte-level observations choose a source write separately for each byte. A read
may then mix bytes from different writes, producing a torn value, subject to
ordering and atomicity restrictions. The instructions still access aligned
four-byte words: byte-level tracking does not add arbitrary byte-sized or
partially overlapping instructions.

The two representations agree when every read has one source for all its bytes.
Under mutual scope coverage of all non-initial operations, a theorem derives
that condition from byte-level validity. Without such a justification, choosing
the simpler representation is an explicit restriction, not a program setting.
The byte-level account keeps unresolved how a mixed-source read counts as
observing a write. It states two interpretations and identifies results proved
under both; Lean checking does not settle which interpretation matches PTX.


