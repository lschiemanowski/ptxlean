# From encoded inputs in memory to an affine error bound

The mixed execution and affine example are implemented in
[`Mixed.lean`](../../integration/torchlean/PtxBinary32/Mixed.lean) and
[`Affine.lean`](../../integration/torchlean/PtxBinary32/Affine.lean).
The authoritative contracts are the Stratic descriptions
`mixed-scalar-execution` and `affine-memory-kernel`. The checks establish these
formal contracts; their restricted source interpretation remains explicit below.

The example computes x*y+b. Its purpose is to join two kinds of existing results:
instructions describe the registers and memory that actually change, while the
numerical adapter describes the error introduced by encoded binary32 arithmetic.
The conclusion should concern the actual word stored by the program. A proof
about an unrelated arithmetic expression would not make that connection.

## Follow the seven instructions

Consider memory whose first four words initially contain binary32 encodings of
1.5, 2.0, 0.25 and an arbitrary old value. The four address registers point to byte
addresses 0, 4, 8 and 12. These are word indices 0, 1, 2 and 3 because each word occupies
four bytes. The value registers can initially contain anything.

| PC | Instruction | Effect in this fixture |
|---|---|---|
| 0 | `ld.relaxed.gpu.global.u32 r0,[a0]` | r0 receives the bits of 1.5 |
| 1 | `ld.relaxed.gpu.global.u32 r1,[a1]` | r1 receives the bits of 2.0 |
| 2 | `ld.relaxed.gpu.global.u32 r2,[a2]` | r2 receives the bits of 0.25 |
| 3 | `mul.rn.f32 r3,r0,r1` | r3 receives the rounded product |
| 4 | `add.rn.f32 r4,r3,r2` | r4 receives the rounded sum |
| 5 | `st.relaxed.gpu.global.u32 [a3],r4` | Output memory receives the actual r4 bits |
| 6 | `exit` | This run explicitly finishes |

In this fixture both arithmetic results, 3.0 and 3.25, are exactly representable.
The universal theorem does not depend on exact representability. It
allows arbitrary encoded inputs, with stronger real-number conclusions under
explicit numerical conditions. `disjoint_example` kernel-checks this actual completed run and its exact final
memory, including the 3.25 output encoding `0x40500000`.

The `.u32` loads and store copy all 32 bits unchanged; they do not convert an
integer into a floating-point value. At a PTX declaration boundary the working
value registers should be `.b32` bit registers, which are compatible with both
instruction types. Simply declaring the registers `.u32` does not make them
compatible with floating-point arithmetic. The current typed interfaces do not
check declarations, so this remains an explicit source boundary.

Multiplication rounds before addition reads its result. Keeping the actual
intermediate word connects the two steps and accounts for two rounding errors.
A fused multiply-add instruction would have a different contract. The explicit
`.rn` spellings select nearest-even rounding at each arithmetic step.

Exit retains PC 6. It does not advance to 7. Thus a finished trace has seven
instruction events but only six advancing steps. Stopping after the store is
still a finite prefix, not a completed run.

## One state, distinct instruction identities

The mixed layer retains `Scalar.State`: a program counter, value
registers, address registers, predicate registers and the arena, a list of memory
words. Instructions have a scalar or binary32 tag. Their events have the same
kind of tag and retain their original instruction occurrence. This avoids
pretending that a floating-point operation was an integer operation.

A dispatch first fetches at the current program counter. A scalar instruction
then uses `Scalar.eval none` exactly; `none` means loads read the current arena.
A binary32 instruction uses its reviewed relational `Eval`. Both positive and
negative predicates retain their original meanings. The concrete affine example
uses no predicates, but the reusable layer must preserve them.

The mixed evaluation result distinguishes advancing, explicit exit, scalar fault
and unsupported operation. A missing program position gives the existing
invalid-PC fault. An unsupported target has no admitted dispatch; the model does
not invent a hardware exception for that exclusion. Unknown scalar instructions
retain the original unsupported behavior even if their predicate is false.

The mixed program requires ISA 9.4 and numeric target sm_70 or later. The arithmetic
leaf alone needs only sm_20, but the chosen scoped relaxed memory instructions
require sm_70. This condition describes a supported feature slice, not a complete
validator for target spellings or architecture-specific suffixes.

## Finite paths and completed runs

The smallest reusable composition interface is a finite path of advancing steps,
followed, when applicable, by one terminal dispatch. A path can be empty or stop
before an instruction that remains to be executed. A completed run requires an
actual exit event. A fault or unsupported operation is a separate terminal result
with no invented event. This avoids introducing a second executable runner just
for this example. It also avoids using fuel exhaustion as a termination proof.

A generic append lemma composes adjacent paths. An invariant lemma lifts a
property preserved by each step through the whole path. A trace witness lemma
recovers the actual pre-state and fetched instruction for each event. These
lemmas must not assume the event labels already have the desired meaning.

Scalar evaluation already proves alignment, complete-access bounds, constant
arena length and preservation of words not stored to. Floating-point evaluation
preserves all memory and emits no memory effect. The mixed proofs lift those
facts through paths, including prefixes that later fault. They do not reimplement
load/store checks or numerical rounding.

## Why arbitrary addresses may coincide

The general example uses any four valid addresses, not only 0, 4, 8, 12.
The only store occurs after all three loads. For example, the output pointer can
be the left-input pointer: r0 retains the old input bits while the final store
replaces that memory slot. The arithmetic still uses the initial input snapshot.

Consequently, there is no need for a pairwise-distinctness premise. The exact
memory postcondition replaces only the output word. All other words are framed,
meaning unchanged. An input slot that aliases the output is allowed to change.
The five working value registers are overwritten before use; other registers,
all address registers and all predicates are preserved.

Arena validity checks four-byte alignment and enough space for the whole word.
It does not establish runtime allocation ownership, permission, initialized
storage, address translation or launch argument correctness. These are external
conditions for using this isolated sequential interpretation. No other thread,
host operation or asynchronous work interferes with the modeled arena. General
concurrent memory observations and overlapping mixed-width accesses remain
outside this example.

## The execution theorem comes before the error theorem

The execution characterization quantifies over every completed run from
the initial layout. It derives actual words `mid` and `out` satisfying:

```
Results .mul left right mid
Results .add mid bias out
final.memory = initial.memory.set outputIndex out
```

It also identifies the exact seven events and their fetched positions, all load
and store addresses and values, the final working registers, and the unchanged
storage. Neither a desired final value nor these result relations belong in the
initial-state assumptions.

The separate `run_exists` proof supplies a completed run for every encoded input.
The numerical reference supplies one allowed result at each arithmetic step.
That witness must not restrict the universal semantics to a single chosen result.
A straight-line control proof establishes that no advancing path has more than
six steps and that all terminal runs from the valid initial layout halt. Short
prefixes remain incomplete. This is bounded control reasoning, not a hardware
scheduling or fairness theorem.

For the numerical corollary, suppose the initial words represent finite reals
xh,yh,bh, and the ideal real inputs are x,y,b. Assume input deviations bounded by
ex,ey,eb and the two input-only guards:

```
|xh*yh| ≤ maxFinite
|xh*yh| + eps32(xh*yh) + |bh| ≤ maxFinite
```

Here `maxFinite` is the largest finite binary32 value. `eps32` is the reviewed
local absolute rounding-error bound. The second guard conservatively reserves
space for the first rounding error and the bias. Both guards concern initial
inputs, not a desired intermediate or final answer.

The existing `Error.affine_results` then makes both stages finite and bounds the
stored real value z by:

```
|z-(x*y+b)| ≤
  eps32(fp32Round(xh*yh)+bh) + eps32(xh*yh)
  + |x|*ey + |y|*ex + ex*ey + eb
```

The first two terms are the two rounding contributions. The next three propagate
the multiplicand errors, including their interaction. The final term is the bias
error. This is an absolute bound; encoded bit equality is a different statement.

NaNs retain the reviewed conservative result envelope. Proving an envelope member
exists is not proving that every such encoding occurs on hardware. Neither this
example nor the numerical library establishes GPU or PyTorch conformance.

## Source and implementation boundaries

The pinned manual is `references/nvidia/ptx-isa-9.4/index.html`, SHA256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
Relevant anchors are `floating-point-instructions-add`,
`floating-point-instructions-mul`, `floating-point-instructions`,
`data-movement-and-conversion-instructions-ld`,
`data-movement-and-conversion-instructions-st`, `operand-type-information`,
`predicated-execution` and `control-flow-instructions-exit`.

The modules are `PtxBinary32/Mixed.lean` and `PtxBinary32/Affine.lean` in
the TorchLean integration package. They consume the existing scalar evaluator,
the binary32 instruction relation and `PtxBinary32Error.lean`. Source review
remains distinct from Lean checking. `run_iff` gives exact execution meaning,
`path_bound` bounds advancing prefixes, and `stored_error` concerns actual final
memory under the stated numerical conditions.


## Memory rules and value grounding

`trace_memory_witness` filters the actual seven-event trace to the three loads
and one store, retaining their original instruction positions 0, 1, 2 and 5. It
proves exact equality with all program-event labels of the separately checked
`Ptx.AffineMemory` witness. Initial-write events are supplied separately, once
per initial arena word. The source proof permits arbitrary aliases: no load can
read from the later store. `run_memory_witness` establishes the same connection
for every admitted terminal run and the word actually found in final memory.

The existing graph-validity conditions are necessary constraints, not an asserted
sufficient model of every dependent PTX program. The concrete program also has
explicit value grounding. `RegisterDependency` uses actual event write/read
lists and does not assume the writer is earlier. `register_dependency_forward`
proves that earlier order for this trace; the resulting relation is acyclic.
`run_grounded` combines the actual initial-input arithmetic dataflow, exact
trace, forward register dependencies and valid memory witness. These are facts
about this program, not a new general no-thin-air axiom or a hardware theorem.

`all_alias_example` kernel-checks the opposite storage layout: all four pointers
name the same initial 1.0 word. The three loads still obtain 1.0 and the sole store
writes the 2.0 encoding `0x40000000`. Both concrete examples derive arithmetic
membership from the encoded reference computation and prove actual completed
instruction runs; they do not assume the expected output relation.
