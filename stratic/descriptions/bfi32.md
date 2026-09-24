# Bit-field insertion

Insert low bits of the first source into the second source, starting at the position specified by the low eight bits of the third source, with length specified by the low eight bits of the fourth. Preserve all other bits; truncate insertion at bit 31. Zero length or starting past bit 31 preserves the second source. Introduced PTX 2.0; requires sm_20.

Bits are numbered from zero, starting with the least significant bit. A word
is a 32-bit value. Each instruction reads its sources before writing its
destination, even if source registers repeat or equal that destination.
A true-or-false guard controls execution. A skipped instruction advances to the
next instruction without writing a register. Both guard polarities are supported.
The execution record preserves the order and repetition of register reads; a
skipped instruction records only its guard read. Memory, address registers,
predicate registers and other word registers remain unchanged.

The target contract selects PTX ISA 9.4 and GPU architecture number SM at least
20. This checks the feature floor, not whether every numeric architecture
name is recognized. Target checks apply even when the guard is false. The typed
decoder accepts exactly the selected spelling and operand shape, preserving
the guard, and distinguishes malformed operands from unsupported spellings.

Sources and destination have compatible declared 32-bit types; immediate words
have already been decoded and size-converted. The leaf does not check raw module
syntax, register declarations, other widths or hardware conformance. Universal
output-bit and execution properties establish the formal contract. Comparison
with the pinned NVIDIA source remains separate from Lean proof validity.
