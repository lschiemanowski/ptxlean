# Scalar message passing

This fragment studies a producer that writes data and a flag, and a consumer
that reads the flag before reading the data. Its programs are finite instruction
lists without branches, called straight-line programs. They store literal
32-bit unsigned integers (`u32`) and load into registers. A four-byte value is a
word; word locations do not overlap, and each begins at an address divisible by
four (alignment). All accesses use global memory on one GPU and GPU scope, which
includes its threads. They use the ordinary memory-access mechanism PTX calls
the generic proxy. Release and acquire are ordering options on stores and loads;
their qualifying instruction patterns establish synchronization. Merely reading
a value written by another thread does not establish it. Literal stores are a
simplified internal representation; actual PTX store data comes from a register.

Executing instructions produces records of reads and writes, called memory
events. A memory graph contains these events, a proposed write supplying each
read's value, and ordering relations. The proposed source must write the same
location and value. The memory-validity rules check this graph; they do not
assume that the consumer sees the desired data.

Several relations express different parts of the check. Program order follows
one thread's instruction sequence. Observation links a qualifying source write to the
read that observes it. Synchronization connects qualifying release/acquire patterns
between threads. Paths combining program order and synchronization form base
causality. Restricting those paths to equal endpoint addresses gives the
proxy-preserved base in this fragment. Causality is either such a restricted
path or an observation followed by one; arbitrary chains of these causality
edges are not silently added. Coherence orders writes to a location.
Communication collects write-to-read source links, coherence links, and links
from a read to writes later than its source. Initial events represent the
starting contents, group the four bytes of each word, and precede program writes
to that location.

Publication means making the written data available to the reader through this
flag protocol. With an acquire flag read, observing the flag guarantees the new
data. A constructed completed execution shows that the rules actually admit a
run; the theorem is not true merely because no run exists. Changing the consumer's
acquire to relaxed ordering admits a completed run that sees the flag but reads
old data, called a stale read. Both variants have safe, aligned accesses under
the same explicit allocation assumptions.

The proof audit lists the axioms and other declarations on which results depend.
The source account explains why one source write per whole word is justified
under these scope restrictions and why fixed literal stores do not depend on
read values to justify their data. Excluded features include separate memory-ordering
instructions (fences), indivisible read-modify-write operations (RMWs), stores or
addresses computed from loads, branches, and operations initiated for later
completion. No hardware scheduling guarantee is claimed.

The guide connects source clauses to definitions and proof steps, distinguishes
formal guarantees from semantic interpretation, and gives reproducible checks.
Finite local execution and admitted completed candidates are distinct from a
general progress theorem for GPU executions.

A finite candidate checker accepts exactly the graphs satisfying these restricted
memory rules, including ordering-path conditions with no fixed path-length limit.
For the message-passing program, a separate result classifies all read outcomes
for both acquire and relaxed consumers. Small programs designed to distinguish
memory rules are called litmus tests. These exercise two threads each storing
before reading the other's location (store buffering), ordering at one location,
and release/acquire patterns spanning several instructions. The proofs construct
permitted outcomes and exclude forbidden ones for all relevant candidates.
