# Byte permutation

A byte is eight bits. Plain `prmt.b32` builds a 32-bit result by selecting four
bytes from two input words. Bytes zero through three come from the first word,
starting at its least significant byte; bytes four through seven come from the
second word in the same order.

Each output byte has a four-bit selector in the control word. Its low three bits
choose the source byte. Its remaining bit selects ordinary copying or sign
replication: filling the output byte with eight copies of the source byte's most
significant bit, producing either zero or 255. The least significant selector
controls the least significant output byte. Only the low sixteen control bits
are used. The control can be a register or an immediate value; it is not limited
to sixteen-bit input values.

All sources are read before the destination is written, so registers may repeat
or overlap the destination. A true-or-false guard controls execution. Skipping
advances the program counter without a write; enabled execution changes only the
destination and that counter. The execution record retains the guard read and
ordered source reads, including repeats, or only the guard read when skipped.
Memory, address registers, predicate registers and other word registers are preserved.

The selected form was introduced in PTX 2.0 and requires SM 20 or higher. Fetched
steps select ISA exactly 9.4 and a numeric SM floor of 20, even when skipped.
This is a feature threshold, not validation of architecture names. The typed
decoder accepts exactly `prmt.b32`, a word-register destination and three word
operands, preserving the guard. Immediates have already been converted to words;
register declarations and raw PTX text are outside this decoder.

The six specialized modes have different selection rules and remain excluded.
Proofs must establish the output-bit law for every input, including arbitrary
upper control bits, and exact guarded execution and decoding. These Lean facts
are separate from source fidelity and do not establish hardware conformance.
