# Computed-data publication

One thread reads two input words that no thread changes, adds them with 32-bit
unsigned wrapping arithmetic, and writes the computed result to a payload word.
It then writes one to a flag using release ordering. A second thread reads the
flag with acquire ordering and then reads the payload. If it sees flag one, its
payload register must contain the sum of the initial input words. This guarantee
covers every choice of read sources and write order satisfying the represented
necessary memory rules, not only one successful example.

The computation uses actual scalar loads, addition, register stores, and exit.
A small ordered instruction wrapper attaches relaxed or acquire ordering to a
load and relaxed or release ordering to a store. Ordering belongs to the fetched
instruction. The wrapper reuses scalar state transitions; its memory labels
retain the value, guard outcome, and original dispatch position. Addresses are
stored as word indices; four-byte alignment proves exact recovery of the original
byte address. A skipped instruction emits no memory event. Typed textual encoding
makes the ordering qualifiers explicit; it is not a raw PTX parser.

Inputs, payload and flag occupy four distinct aligned global-memory words at
byte addresses zero, four, eight and twelve. The flag is initially zero; other
initial words and both threads' registers are arbitrary. Both threads execute
straight-line code on one GPU. All memory operations use GPU scope and the
generic access mechanism, called the generic proxy. PTX relaxed, acquire and
release forms require PTX version 6.0 and target sm_70 or newer. No aliases,
mixed-size accesses, atomics, asynchronous operations or scheduler fairness are
included. Access safety means alignment and bounds within this initialized arena;
it does not establish allocation ownership or hardware launch validity.

The producer's input reads can only obtain values from initialization: no program
instruction writes those addresses. The result is then determined by addition,
and the flag store is a constant moved into a register. The consumer never writes.
This explicit ordering of value dependencies prevents a value being justified
only by a cycle in this example. It does not settle the general PTX rule against
such circular justification. Graph validity remains a set of necessary memory
constraints for dependent programs, not a claimed sufficient general PTX model.

A constructive witness supplies both completed scalar runs and compatible memory
sources and write order for every input pair. Replacing only the consumer flag
load with relaxed ordering also has a witness that sees flag one but the old
payload. Whenever the old payload differs from the computed sum, that witness
violates the acquire result. Separate safety proofs cover every candidate run,
including candidates later rejected by the memory rules. Extended explanations
show how instructions generate events and how synchronization forces the result.
