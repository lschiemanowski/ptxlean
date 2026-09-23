# Unsigned minimum and maximum

The `min.u32` and `max.u32` instructions select the smaller or larger of two
32-bit values interpreted as unsigned numbers. Every bit pattern is valid,
including values with the top bit set. The result is one of the operands;
there is no overflow condition and equal operands return their common value.
Other widths, signed comparisons, packed values and modifiers are outside this
first form-level contract.

These instructions use the existing scalar binary-operation interface. Both
operands are read from the incoming state before writing the destination, even
when a source and destination are the same register. Execution preserves other
registers and memory and advances to the next instruction. A false predicate
skips the write. The instruction emits no memory event. The typed text interface
accepts a word-register destination and register or immediate word sources,
rejects malformed operand lists, and preserves guarded encode/decode round trips.
It does not validate declarations in raw PTX source.

Proofs characterize both results for arbitrary operands as the mathematical
unsigned minimum or maximum. They also establish operand selection,
commutativity, repeated-input behavior and bounds, and connect these value facts
to actual scalar execution and state preservation. Boundary examples distinguish
unsigned from signed comparison. The source requires PTX 1.0 and supports all
targets for these selected forms; this source condition is distinct from the
existing memory-only instruction eligibility checker.

Smaller-model submissions are checked against these obligations and the pinned
instruction sections. A successful proof build alone does not establish source
fidelity, and accepting these two forms does not complete the wider min/max
families.
