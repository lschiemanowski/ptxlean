# Funnel shifts and rotations

A funnel shift joins two 32-bit words, shifts that 64-bit value, and returns
one 32-bit half. The first source supplies the low half; the second supplies
the high half. Left shifts return the high half and right shifts return the low
half. Bits entering the combined value are zero.

The count is an unsigned 32-bit word. Clamp mode caps it at 32; wrap mode uses
its remainder after division by 32. At count zero, left returns the second
source and right returns the first. At clamped count 32 these choices reverse;
wrapped count 32 acts like zero. Every source and count bit pattern is allowed.

Reading the same word as both sources in wrap mode rotates its bits: bits shifted
out of one end reappear at the other end. The rotation example uses an input
register twice and overwrites that register, then exits. Its result is specified
by Lean's standard word rotation, for arbitrary input and count. It provides a
finite execution witness and a correctness result for every completed execution,
while preserving memory and other registers. It models a sequential register-only
kernel. Register 0 contains the word and receives the result; register 1 contains
the runtime count. The example inherits the existing combined-kernel interface's
ISA9.4 and SM70 floor, which is stricter than this instruction's SM32 floor.
There is no device launch or hardware-conformance claim.

The four spellings are `shf.l.clamp.b32`, `shf.l.wrap.b32`, `shf.r.clamp.b32`
and `shf.r.wrap.b32`. A typed decoder accepts exactly a word-register destination
and three word operands, preserving the true-or-false execution guard. Immediates
are already converted to words; raw text and register declarations are outside
this boundary. Sources are read before any destination write, allowing repeats
and overlap. Executed instructions retain ordered source reads; skipped
instructions retain only the guard read and advance only the program counter.
Memory, address registers, predicates and other value registers are unchanged.

These forms were introduced in PTX 3.1 and require SM32 or higher. Fetched steps
require ISA exactly 9.4 and numeric SM at least 32, even when skipped. This is a
feature threshold rather than validation of architecture names. Universal result,
execution and decoder proofs establish the Lean contract. Reviewing that contract
against NVIDIA's documented meaning remains a separate obligation.
