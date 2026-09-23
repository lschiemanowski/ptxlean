# Reusable publication rules

A producer publishes data by writing it and then writing a flag with release
ordering. A consumer reads that flag with acquire ordering before reading the
data. The flag communicates that the earlier data write is ready to observe.
Reading a flag value is sufficient only when that value identifies the relevant
release write; equal values from unrelated writes must not be confused.

These rules operate on the whole-word memory graph. All participating program
accesses use the generic proxy, global storage, GPU scope and one device, with
matching aligned four-byte accesses. The graph records which write supplies each
read, and a separate order of writes to each location, called coherence. Program
order and release/acquire synchronization give a path between the producer's
data write and the consumer's data read. Their matching address turns that path
into the causality relation used by the memory rules.

If the read can take its value only from initialization or from the published
write, causality rules out initialization: initialization precedes that write in
coherence. The conclusion identifies the source write, and then its exact value.
The same reasoning applies with more writes when every alternative source is
proved to precede the published write in coherence. The rules do not assume the
value that the read should return.

These are conditional results about memory graphs. An application must connect
the graph's events to its actual instruction executions, establish the possible
source writes, and prove memory safety and execution existence separately. The
rules do not add a general treatment of circular data dependencies, different
access sizes, other scopes or proxies, scheduling progress, or hardware behavior.
