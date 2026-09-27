# Rounded reciprocal instruction

The reciprocal of a number x is one divided by x. This instruction responsibility
covers the explicit PTX spelling rcp.rn.f32: a reciprocal in binary32, the
standard 32-bit floating-point format, rounded to the
nearest representable result, resolving halfway cases toward an even final bit.
It preserves subnormal numbers, the small representable values near zero.
The target policy is the pinned PTX 9.4 version on sm_20 or later, where sm_20
denotes NVIDIA compute-capability level 2.0.
Other rounding modes, approximation, flushing small values to zero, and other
number formats are rejected rather than silently treated as this instruction.

The instruction reads one operand from the original scalar state and writes
one word register. That operand can be a register or an already decoded exact
floating-point bit literal. Reading and writing the same register is permitted.
An optional predicate, a true-or-false condition, chooses whether to execute: a false predicate advances the
instruction position without requiring arithmetic and preserves every register.
An enabled instruction advances and writes an output permitted by the numerical
reciprocal relation. Other registers, address registers, predicates and memory
remain unchanged. The occurrence records the actual instruction position,
executed instruction, reads, writes and absence of memory access.

Execution of an instruction in a program requires that the instruction actually
occurs at the current program position and that the target policy holds. Every
fetched instruction on a supported target has a next state; this is one-step
existence, not a whole-kernel termination or hardware progress guarantee.

The numerical provider is encoded division of one by the operand, including
signed zeros and infinities. NaN, meaning not a number, results use the existing
conservative allowance for alternative NaN bit patterns. The instruction must
retain that freedom rather than substitute one NaN payload. Finite real equality
and accuracy follow separately under the provider's finite-input, nonzero and
range conditions. Neither ordinary execution nor a disabled predicate requires
those numerical-analysis conditions.

The text interface accepts a typed statement containing the exact mnemonic,
word-register destination and one word operand. It is not a raw PTX parser or a
checker for register declarations and initialization. The supplied register
bank represents compatible f32 floating-point or b32 untyped 32-bit registers; integer-to-float conversion is not
implicit. The numeric target check does not validate every real GPU target name.
Instruction source review, checked Lean proofs and hardware conformance remain
different claims.
