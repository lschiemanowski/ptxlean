# Whole-word observations

This model records one source write for each complete four-byte read. It uses
the thread scopes and ordering rules described by its parent. A source is an
identity of a particular write event, not merely a numerical value; two writes
storing the same number remain distinct possible sources.

The whole-word model chooses one write as the source of each complete read.
When scopes exclude one another, this represents only reads that do not mix
bytes from different writes; such mixed reads are called torn reads. It does
not enumerate every bytewise outcome. When all non-initial operations mutually
include one another in scope, a theorem identifies this model's validity rules
with those of the original restricted GPU-scoped model.

## Sources and ordering

The source of a read must be a write to the same word with the same value.
Initial events represent the supplied starting contents, one event per word,
and precede later writes to that word. Program order follows each thread's
instruction sequence. Observation links a source write to its read when the pair
meets the same-word and scope or local-order conditions for moral strength.

Synchronization connects qualifying release and acquire patterns between
threads. Paths through program order and synchronization form base causality.
Keeping paths whose endpoints have the same address gives the proxy-preserved
base for this fragment. Causality consists of such a path or an observation
followed by such a path; it does not automatically include arbitrary chains
of causality edges.

Communication combines write-to-read source links, coherence links between
writes, and links from a read to writes later than its source. The validity
rules require compatible sources and coherent write ordering, exclude cycles
in base causality, and make write ordering respect causality. A read cannot
choose a causally future source or a source made obsolete by a causally prior
write. Cycles combining same-address program order and morally strong
communication are also forbidden. These are checks on the proposed graph,
not assumptions that its result is correct.

## Connecting the graph to an execution

The separate scoped memory model checks proposed thread executions against rules
for their reads and writes. To accept a proposed execution, it checks that accesses fit the supplied list
of memory words, that thread identities are distinct, and that the memory rules hold. It does not automatically
include the general allocation checker or instruction-eligibility checker;
combining them requires an explicit proof.

Scope labels supplement records of instructions that actually ran. The current
program connection uses the fixed-address, constant-store language and supplied
initial registers and memory. Memory is a list of four-byte words; distinct
used threads must have distinct identities in the environment. This connection
does not establish all possible executions of general data-dependent programs.

The represented memory instructions use relaxed, release, or acquire ordering.
Release and acquire are options used by a writer and reader to establish ordering
between threads; relaxed accesses do not by themselves provide that pair of
synchronization endpoints. In the flag-and-result example, observing a released
flag with an acquire read guarantees the new result under the model's memory
constraints and mutual scope condition. With the threads in different CTAs and
both operations using CTA scope, a permitted execution can read the flag yet
still observe the old result.

## When this simpler representation is justified

Repeating each whole-word source for all four bytes gives a byte-level graph
with exactly the same validity. Conversely, if every byte of each read in a
byte-level graph selects the same write, selecting that write recovers the
whole-word validity conditions. Equality of byte values alone is insufficient:
the source write identities must agree.

Mutual scope coverage of all non-initial events makes valid byte-level reads
choose one source for the entire word. Under that condition, the whole-word
representation loses no valid byte-source choices within this fragment. The
proofs also connect it to the original restricted GPU-scoped message-passing
model. They establish relationships between formal models; they do not remove
the stated instruction restrictions or prove hardware conformance.

## Additional synchronization order

Collective instructions require ordering beyond release/acquire pairs. An
extension can add base-order edges justified by a completed collective operation.
The same memory constraints then apply to the enlarged base relation: same-address
preservation still happens after building paths, and causality is still not
arbitrarily closed under chaining. Adding edges does not remove any existing
validity requirement. Each use must prove where its added edges came from; an
arbitrary relation supplied by a caller is not a completed PTX semantics.
