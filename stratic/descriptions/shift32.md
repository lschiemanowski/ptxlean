# Selected 32-bit shifts

This family accepts shl.b32, shr.u32 and shr.s32: left shift, right shift filled
with zeros, and right shift filled with the input's sign bit. The count is an
unsigned 32-bit value. Counts at least 32 clear the result, except that signed
right shift produces all ones for a negative input. Counts do not wrap.
All input bit patterns are admitted. Sources are read before any destination
write, so repeated sources and overlap with the destination are allowed.

The common pure-instruction rules preserve guards of either polarity, advance
the program counter and record direct register reads. A skipped instruction
writes no register. Fetched steps require ISA 9.4 and numeric SM at least 10,
even when the guard is false. This selects a feature floor, not valid GPU names.

The typed decoder accepts exactly these three spellings with a word-register
destination and two word inputs. A recognized spelling with malformed operands
is distinguished from an unsupported spelling. Declarations and immediate-value
conversion are supplied by the caller. Other widths and shr.b32 remain outside
this interface; being unsupported here does not make a spelling illegal PTX.

Universal result, frame, determinism, decoder and one-step existence proofs
are separate from source-fidelity review and from whole-program correctness.
