# The upper half of an integer product

Multiplying two 32-bit integers can require 64 bits. The selected `mul.hi.u32`
and `mul.hi.s32` instructions return the upper 32 bits of that full product.
The unsigned form treats each input as a number from zero to 2^32-1. The signed
form uses two's complement: a word whose highest bit is set represents a negative
number. The signed high half corresponds to division by 2^32 rounded downward,
including for negative products. It does not mean truncation toward zero.

All input patterns and coinciding source/destination registers are allowed.
The shared pure instruction rules preserve guards, source order, repeated reads
and unchanged state outside the destination and next instruction position.
The typed decoder accepts exactly these two spellings. Low-half multiplication,
full-width results, other widths and saturation are outside this leaf.

The slice selects PTX ISA 9.4 and numeric SM at least 10; these forms were
introduced in PTX 1.0 and have no additional feature restriction. Compatible
register declarations and already converted immediate values are supplied by
the caller. The numeric floor does not validate target names. Source fidelity,
Lean proof validity and whole-kernel correctness are separate obligations.
