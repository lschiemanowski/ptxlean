# Counting bits in a word

Population count means the number of bits equal to one. Leading-zero count means
the number of consecutive zero bits starting at a word's most significant end,
which is its leftmost end when written in binary. These are different operations:
for the 32-bit word containing the number one, population count is one and
leading-zero count is thirty-one.

The slice supports exactly `popc.b32` and `clz.b32`. Each reads one
32-bit word from a register or literal and writes a count to a 32-bit destination
register. The `b32` suffix describes the input's bits; the result is an unsigned
32-bit integer. Every input bit pattern is valid. Population count of zero is
zero; leading-zero count of zero is thirty-two. Both results lie between zero
and thirty-two, inclusive. These forms require PTX version 2.0 or later and a
target GPU at least `sm_20`.

A unary operation has one input. It uses the scalar machine's existing
incoming-state register reads, destination update, predicates and trace records.
Reading and writing the same register must use its old value as input. Executing
an instruction changes only its destination value and advances the program
counter. Skipping it under a false predicate advances the counter without
reading the data operand or writing a register. Neither operation accesses memory.

The mathematical contracts count true bits at positions zero through thirty-one,
or the consecutive false bits encountered from position thirty-one down to zero.
They apply to every word, not only selected examples. Execution proofs connect
those counts to the actual destination and show what remains unchanged. Independent
checks cover zero, the highest bit, all-one and mixed patterns, overlapping input
and output registers, predicates, and the typed text interface.

Only the exact two mnemonics are supported by this slice. The typed interface
requires a register destination and one word operand; it distinguishes malformed
operands from unsupported mnemonics. The 64-bit variants, other spellings and
modifiers remain outside this slice, even where PTX supports them. Raw text parsing,
register declarations and general architecture eligibility checking remain separate
responsibilities. Lean checking establishes the stated formal results; comparing
definitions and their bit order with the pinned PTX source establishes the separate
case for semantic fidelity.
