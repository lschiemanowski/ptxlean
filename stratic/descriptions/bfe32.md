# Extracting a field of bits

The selected `bfe.u32` and `bfe.s32` instructions take an input word, a starting
bit position and a field length. Bit zero is the least significant bit. Only
the low eight bits of the position and length matter, giving values from zero
through 255. A zero length produces zero, including when the input is negative.

The unsigned form copies the selected bits and fills the remaining result bits
with zeros. The signed form fills them with the field's highest bit. If the
field reaches beyond the input, it uses input bit 31 for that fill. Starting
beyond the input can therefore produce all ones for a negative signed input.
Every input word, position and length is admitted; large operands are not
silently excluded by preconditions.

Sources are read before the destination is changed. Aliases and repeated sources
are allowed. Shared pure instruction rules handle guards, recorded register
accesses and preservation of other state. The typed decoder accepts only the
two selected spellings. Other widths are excluded. The manual's example spelling
`bfe.b32` is not accepted because it is absent from the instruction's syntax.

The selected version is PTX ISA 9.4 and numeric SM at least 20; this instruction
was introduced in PTX 2.0. Compatible register declarations and already converted
immediate values are caller obligations. The numeric floor does not validate
actual target names. Source fidelity, Lean proof validity and whole-kernel
correctness are separate obligations.
