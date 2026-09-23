# From encoded arithmetic to an instruction step

This guide explains the checked instruction contract implemented in
`integration/torchlean/PtxBinary32/Instructions.lean`. The exact worker patch
passed fresh replay and independent source and proof review; those checks are
recorded separately from hardware conformance.

The [numerical foundation](binary32.md) relates input and output bit patterns.
An instruction adds the program position, operands, predicate and destination
register. Consider this typed PTX operation with value registers declared `.b32`:

```ptx
@%p7 mul.rn.f32 %r2, %r2, %r3;
```

Suppose the supplied initial state contains:

| Component | Incoming value | After an executed step |
| --- | --- | --- |
| Program counter | 5 | 6 |
| Predicate `%p7` | true | true |
| `%r2` | `0x3fc00000`, representing 1.5 | `0x40580000`, representing 3.375 |
| `%r3` | `0x40100000`, representing 2.25 | unchanged |
| Memory, address registers, other value registers | arbitrary | unchanged |

The destination is also the first input. Both inputs are read from the incoming
state, so the operation uses 1.5 and 2.25. There is no restriction forbidding
this overlap. The instruction's `.f32` type interprets the bits as floating-point
values; it does not convert the unsigned integers with those bit patterns into
floating-point numbers. Compatible `.b32` register declarations are consequential
when the same register bank also carries integer-typed memory transfers.

The recorded occurrence retains the multiplication instruction at position 5.
It lists reads of predicate 7 and value registers 2 and 3, one write to value
register 2, and no memory effect. If the predicate is false, the program counter
still advances but all registers and memory remain unchanged; the occurrence
lists only the predicate read. A negated predicate uses the opposite condition.

The leaf execution relation accepts every output admitted by the numerical
contract. For finite results the bits are fixed. A NaN result retains the
documented conservative envelope, rather than inheriting one software-selected
payload. The [source review](../formalization/binary32-instructions-source-review.md)
distinguishes that envelope from an exact claim about hardware NaN outputs.
Nonempty arithmetic results establish a next state for every supplied operand
pattern; that is not a GPU scheduling or termination theorem.

The fetched-step relation checks that this instruction is actually at the
incoming program position. Its target boundary is ISA 9.4 and the numeric
`sm_20+` feature condition. These arithmetic-only instruction lists have no exit
operation; falling off the list gives no fetched step. A complete kernel needs
an execution layer that also handles memory instructions, explicit exit and
error outcomes. The existing scoped memory forms have the stricter `sm_70+`
requirement.

The typed decoder accepts the two exact names `add.rn.f32` and `mul.rn.f32`.
It consumes classified operands, not raw source text. Exact-bit immediates
correspond to PTX `0f`/`0F` literals with eight hexadecimal digits; decimal parsing,
register declarations and initialization are separate frontend obligations.
Malformed operands for a supported name differ from an unsupported instruction
name. Other modifiers are not silently discarded.

For numerical reasoning, the destination theorem returns the original result
relation on the actual post-state register. The range and error theorems can then
be applied to that word using facts about the incoming operands. This separates
the instruction proof from the numerical proof without assuming that the
destination already contains the desired answer.
