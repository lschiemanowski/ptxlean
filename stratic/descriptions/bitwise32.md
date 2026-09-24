# Binary bitwise instructions

This family implements only and.b32, or.b32 and xor.b32. Each result bit is respectively the conjunction, disjunction or exclusive-or of the two source bits.
All 32-bit words are admitted, including zero and values with the highest bit set.
No interpretation as a signed integer or floating-point number changes these bits.

The family reuses the pure-instruction execution rules. Sources are read from the
incoming state before the destination is written, including when source and
destination name the same register. A guard decides whether to execute; either
polarity is supported. A skipped instruction advances only the program counter.
Enabled operand-read records retain the guard and every named source, including
repeated registers. These records are syntactic reads, not a complete PTX memory
dependency analysis.

The typed frontend accepts exactly the selected spellings and word operand shapes.
A malformed use of a recognized spelling is distinguished from an unsupported
spelling. Register declarations and immediate conversion have already been
checked by the caller: a word literal is a decoded 32-bit value, not arbitrary
raw PTX text. Other widths, predicate-valued forms and raw module parsing remain
outside the family.

The target slice requires PTX ISA 9.4 and a numeric GPU feature level of at least
sm_10. The selected instructions require no extra feature threshold in the pinned
manual. This numerical condition does not validate real target names or current
assembler support for historical GPUs. It applies to fetched instructions even
when a guard is false.

Proofs establish the exact result, preserved state, determinism, one-step
existence and origin in the fetched program. Source review separately establishes
whether these definitions match the selected PTX forms. The family alone provides
no whole-kernel termination or hardware correspondence claim.
