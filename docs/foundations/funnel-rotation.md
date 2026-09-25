# Funnel shift, then exit

This example rotates a 32-bit word, moving bits that leave one end back into the
other end. Its mathematical interface is `(word : BitVec 32, count : BitVec 32)
→ BitVec 32`, with a choice of left or right rotation. Every count is allowed.
The executable interface puts the word in register 0 and the unsigned runtime
count in register 1; the result overwrites register 0.

Run it from the project root with the pinned Lean toolchain installed:

```sh
lake build
lake env lean examples/funnel_rotation.lean
```

The four printed integers are `878082066`, `2014458966`, `878082066` and
`305419896`; the unchanged memory prints `[17, 23]`. They correspond to rotating
`0x12345678` left by 8, right by 8, left by 40 and left by 32. Count 40 wraps to
8, and count 32 wraps to zero. These are CPU evaluations of the formal instruction
computation, not GPU executions or a PTX assembler test.

## Why two equal sources rotate

A funnel shift takes two words. The first is the low half of a joined 64-bit
value and the second is the high half. Left funnel shift returns the high half
after shifting; right funnel shift returns the low half. With equal sources,
a bit that moves out of one copy enters from the other copy.

The program is a selected wrap-mode instruction followed by exit:

```ptx
shf.l.wrap.b32 r0, r0, r0, r1;
exit;
```

For right rotation, the instruction is `shf.r.wrap.b32`. This notation explains
the instruction sequence; the example constructs typed instructions directly.
It does not parse a raw PTX module or provide a launch wrapper. Clamp-mode funnel
shifts are also verified in the instruction family, but they cap counts at 32
instead of reducing them modulo 32. They cannot replace wrap-mode rotation for
arbitrary counts above 32.

## What the proofs connect

[Ptx/Shf32.lean](../../Ptx/Shf32.lean) defines and proves all four funnel-shift
forms. Its result equations hold for every input word and unsigned count, and
its execution rules read every source before writing the destination. Repeated
input registers and an overlapping destination are therefore admitted.

[Ptx/FunnelRotation.lean](../../Ptx/FunnelRotation.lean) connects the wrap forms
to Lean's standard `BitVec.rotateLeft` and `BitVec.rotateRight` definitions through
`compute_rotation`. This specification is distinct from evaluating the leaf's
`compute` function. `execute` computes the final state of this particular program;
`execution` proves that this state is reached by a real instruction step and exit
in the existing `PureKernel.Run` relation. The trace retains both reads of register
0, the read of register 1, and the exit event.

`execution_exists` provides a completed run for arbitrary incoming register banks,
memory and count. `correct` shows that every completed run agrees with the standard
rotation and halts, ruling out purported fault or unsupported terminal outcomes
under the stated target condition. `frame` preserves memory, address registers,
predicates and every word register except register 0. `no_memory_access` proves
that neither event accesses memory; no allocation or initialization assumption
is required for this register-only example.

The leaf selects ISA9.4 and SM32 or higher. The example inherits the existing
combined-kernel interface's stricter ISA9.4/SM70 condition. Neither theorem checks
architecture-name syntax, proves device scheduling or establishes hardware
conformance. Source review remains separate from Lean checking; see the
[funnel-shift source review](../formalization/shf-source-review.md).
