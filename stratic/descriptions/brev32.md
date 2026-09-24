# Reversing the bits in a word

The selected `brev.b32` instruction reverses the order of all 32 bits. The bit
at position zero (the least significant bit) moves to position 31, and vice
versa. This does not merely reverse the order of four bytes.

Every input bit pattern is allowed. The result is one 32-bit word. The source is
read before writing the destination, so the registers may coincide. The shared
pure instruction rules handle guards, recorded register accesses and preservation
of other state. The typed decoder accepts only `brev.b32`; 64-bit reversal is
outside this leaf.

The selected version is PTX ISA 9.4 with numeric SM at least 20. The instruction
was introduced in PTX 2.0. The numeric condition records a feature requirement,
not validation of a GPU's target name. Compatible register declarations and
already converted immediate values are supplied by the caller. Source fidelity,
Lean proof validity and whole-kernel correctness are separate obligations.
