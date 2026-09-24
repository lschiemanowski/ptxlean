# Three-input Boolean operations

Apply an eight-entry Boolean truth table independently to each of the 32 bit positions. The first input chooses weight four in the table index, the second weight two and the third weight one. The table is an immediate integer in 0..255. Only plain lop3.b32 is selected; no predicate result, BoolOp qualifier or sink destination. Introduced PTX 4.3; requires sm_50.

Bits are numbered from zero, starting with the least significant bit. A word
is a 32-bit value. Each instruction reads its sources before writing its
destination, even if source registers repeat or equal that destination.
A true-or-false guard controls execution. A skipped instruction advances to the
next instruction without writing a register. Both guard polarities are supported.
The execution record preserves the order and repetition of register reads; a
skipped instruction records only its guard read. Memory, address registers,
predicate registers and other word registers remain unchanged.

The eight-bit table is part of the instruction, not a fourth runtime register
read. Its bit at index 4*a + 2*b + c supplies the output for input bits a, b, c.
For example, table 0xF0 returns the first input and 0xAA the third. The typed
decoder accepts only an immediate table in 0..255 and a word-register destination.
Predicate-producing variants and a discarded destination remain unsupported.

The target contract selects PTX ISA 9.4 and GPU architecture number SM at least
50. This checks the feature floor, not whether every numeric architecture
name is recognized. Target checks apply even when the guard is false. The typed
decoder accepts exactly the selected spelling and operand shape, preserving
the guard, and distinguishes malformed operands from unsupported spellings.

Sources and destination have compatible declared 32-bit types; immediate words
have already been decoded and size-converted. The leaf does not check raw module
syntax, register declarations, other widths or hardware conformance. Universal
output-bit and execution properties establish the formal contract. Comparison
with the pinned NVIDIA source remains separate from Lean proof validity.
