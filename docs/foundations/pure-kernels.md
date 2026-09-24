# From reviewed instructions to a complete kernel

The [Stratic description](../../stratic/descriptions/pure-kernel.md) explains the
execution contract. This guide walks through the [mask-and-select example](../../stratic/descriptions/mask-select.md).
Its function has signature **`(x y mask : BitVec 32) → BitVec 32`**:

```text
masked = x AND mask
result = if masked == 0 then y else masked
```

`BitVec 32` represents exactly 32 bits. No input needs to be small, nonnegative
under a signed interpretation, or represent a floating-point number. For example,
masking `0x1234` with `0xff` gives `0x34`; masking `0x100` gives zero, so the
second input is returned instead.

Run the examples from the repository root using its pinned Lean installation:

```sh
lake build
lake env lean examples/mask_select.lean
```

The two printed decimal results are `52` and `99`. The command also prints the
main theorem signatures. To run the full source, evidence and dependency checks,
use `bash scripts/check.sh` after acquiring the pinned manual as described in the
README. The optional TorchLean integration has its own check command.

## Follow the seven instructions

Initial memory contains `[x, y, oldOutput] ++ tail`. The tail and all initial
register values are arbitrary. The initial program counter is zero. The mask is
an immediate input to this specialized program; the kernel loads x and y from
memory. All memory addresses in this example are byte addresses.

| PC | Instruction | State after the instruction |
| --- | --- | --- |
| 0 | Load word at address 0 into r0 | r0 contains x |
| 1 | Load word at address 4 into r1 | r1 contains y |
| 2 | `and.b32 r0, r0, mask` | r0 contains the masked word |
| 3 | Compare r0 with zero, producing predicate p0 | p0 says whether the masked word is zero |
| 4 | `selp.b32 r2, r1, r0, p0` | r2 contains the fallback y when p0 is true, otherwise the masked word |
| 5 | Store r2 at address 8 | Only the third memory word changes |
| 6 | Exit | A completed run ends with its exit event |

A predicate is a true-or-false register. The selection predicate is an input to
`selp`, distinct from an instruction guard that decides whether to execute an
instruction at all. The example executes every instruction. Its AND deliberately
reads and writes r0, checking that operands are read before the destination changes.

[`MaskSelect.lean`](../../Ptx/MaskSelect.lean) defines the program and each
intermediate state. `execution` constructs the whole trace. `correct` uses the
catalog's proved determinism to show that every completed run agrees with that
trace, including that no completed run ends in a fault. `execution_exists`
separately supplies a halted execution. `output_correct` states the output word;
`other_memory` preserves each other word. `memory_safe` applies the shared bounds
proof to every emitted memory effect. None of these results assumes the final
output as a premise.

## The reusable connection

[`PureKernel.lean`](../../Ptx/PureKernel.lean) accepts a catalog: a collection
naming each instruction family and its existing semantics. Instructions and
events retain their family identity. The selected value is constrained by that
family's result relation, so a family admitting two values still has two possible
next states. `dispatch_preserves_choices` proves this explicitly. Determinism is
an additional property, proved for the concrete reviewed catalog and never
required by the general execution model.

[`ReviewedPure.lean`](../../Ptx/ReviewedPure.lean) supplies the current bitwise,
unary, selection, signed min/max, shift, bit-reversal, high-half multiplication
and bit-field extraction families. Each adapter uses the
original leaf's lowering and results directly. Its bitwise correspondence proves
both directions of state-step agreement with the older scalar operations and
matches program counter, execution flag, reads, writes and memory metadata.
Instruction identities remain distinct. The older left/unsigned-right shift
value definitions also agree on all inputs.

The finite-prefix rules were moved unchanged from the binary32 mixed model into
[`ExecutionPath.lean`](../../Ptx/ExecutionPath.lean). Existing public Lean names
remain under `Ptx.Scalar.Mixed` for compatibility. Both execution models import
those same rules. Scalar memory transitions and frame proofs are reused rather
than replaced. This is a small extraction, not a redesign of floating arithmetic.

## Read the boundaries literally

The composed arena selects ISA 9.4 and numeric SM at least 70 because of its
scalar memory forms. It additionally checks the particular pure family's target
condition even when its guard is false. Unsupported domain/family cases produce
an explicit implementation-boundary outcome; this is not a prediction of a GPU
fault. The existing binary32 mixed relation retains its earlier target-admission
convention; only its common finite-path definitions moved.

Memory is a supplied, initialized list of words with concrete sequential reads.
This example does not establish allocation, launch or raw-PTX parsing correctness,
or general concurrent memory admission. A finite prefix is not an exit, and a
next-step existence theorem does not make every looping program terminate.
[`PureKernelExamples.lean`](../../Ptx/PureKernelExamples.lean) checks branching
past an unsupported instruction, a missing program counter, misaligned memory,
a rejected target despite a false guard, and two permitted pure results.

The [shift trial](../../formalization/results/shift32/README.md) records what Luna
produced, what the fixed GLM reviewer said, and the independent checks required
before acceptance. The proof of a result and the review of its PTX interpretation
remain separate evidence.

The [array walkthrough](array-mask-select.md) extends this computation to an
in-place loop of arbitrary bounded length, with preserved surrounding memory
and a proof excluding infinite instruction executions.
