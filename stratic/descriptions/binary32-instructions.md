# Binary32 addition and multiplication instructions

This instruction layer connects two PTX operations to binary32, the 32-bit
single-precision number format:
`add.rn.f32` adds two single-precision values, and `mul.rn.f32` multiplies them.
Each rounds to the nearest representable result, choosing the even last bit at
an exact tie. Small values called subnormal numbers are retained rather than
flushed to zero. The selected source is PTX ISA 9.4, with the numeric target
condition `sm ≥ 20`. This condition selects arithmetic features; it does not
validate GPU target names or architecture suffixes.

Instructions use the existing scalar state: a program counter identifying the
next instruction, value registers, address registers, predicates and memory.
An optional predicate is a true/false guard, which can also be negated. A true
guard reads both operands from the incoming state and writes only the destination
value register. This remains true when either input register is also the
destination. A false guard preserves every register. Both cases advance the
program counter by one and preserve all memory, addresses and predicates.

The arithmetic result is any word admitted by the encoded binary32 result
contract. Ordinary results keep the reference bits, including signed zero and
infinity. If the reference is a NaN, meaning “not a number,” every NaN encoding
is included conservatively. This freedom must not be replaced by one chosen
payload, the bits distinguishing NaNs. Membership in this result set does not
establish that every included NaN can occur on hardware. A signaling NaN is marked
to request an invalid-arithmetic signal in the floating-point standard; a quiet
NaN is not. Which output encodings PTX can produce remains a source question.
Existing numerical bounds apply once their finite-input and range conditions
are established.

The step record retains the actual floating-point instruction and its position.
It lists the guard register and, only when the instruction executes, its operand
registers and destination write. It records no memory effect. Fetch must obtain
that same instruction from the current program position, and the selected target
condition must hold. A missing instruction admits no step. A list of these two
instruction forms has no exit operation: reaching its end does not establish
kernel completion. Existence means that the specified instruction relation has
a next state, without a hardware progress or scheduling claim.

The text boundary accepts already classified operands with exactly the two
explicitly rounded instruction names above. Each destination is a value register;
each source is a value register or an already decoded exact binary32 bit literal,
as written `0f` or `0F` followed by eight hexadecimal digits. These bits are not
converted from an integer value. Value registers here represent `.b32` bit
registers or compatible `.f32` floating-point registers, not arbitrary declared
`.u32` or `.s32` registers. Checking declarations and initialization is a separate
frontend obligation. Decoding and encoding agree in both directions. Wrong
operands for a supported name are distinguished from an unsupported name.

Other rounding modes, flushing small values to zero, saturation (clamping the
result to a limited range), double precision, two values packed into one operand,
and instruction names without explicit rounding are outside this slice. So is
multiply-add fusion, which combines the two operations into one rounding. It does not add a raw PTX parser, a mixed-instruction runner, numerical
range analysis, whole-kernel correctness, or hardware conformance. Instruction
proofs and the review of their fidelity to the pinned manual remain separate.
