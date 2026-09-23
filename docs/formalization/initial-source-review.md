# Source review for the first instruction-formalization tasks

This review was prepared independently of the generating worker. Its normative
input is the [pinned PTX ISA 9.4 manual](../../references/nvidia/ptx-isa-9.4/README.md),
SHA-256 `0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
`python3 scripts/check_sources.py` verified the artifact before this review.
Source correspondence remains a reviewed interpretation of the manual, separate
from Lean proof checking or hardware conformance.

## Recommended task sequence

| Task | Exact forms | Source | Conditions and distinguishing cases |
| --- | --- | --- | --- |
| First: unsigned minimum and maximum | `min.u32`, `max.u32`, no modifiers | [§9.7.1.13](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-min), [§9.7.1.14](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-max); HTML lines 9521–9684 | PTX 1.0; all targets. Select by unsigned order, including the high-bit boundary. Fits the existing binary-operation interface. |
| Next: bit counts | `popc.b32`, `clz.b32` | [§9.7.1.15](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-popc), [§9.7.1.16](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-clz); lines 9685–9762 | PTX 2.0, `sm_20` or later. Both return a `.u32` count. `popc` counts all one bits; `clz` starts at the most-significant bit. Zero gives 0 and 32 respectively. Requires a reviewed unary-operation interface. |
| Then: bit reversal | `brev.b32` | [§9.7.1.19](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions-brev); lines 9869–9902 | PTX 2.0, `sm_20` or later. Output bit `i` equals input bit `31-i`; this is bit reversal, not reversal of the four bytes. Reversing twice recovers the input. Reuses the unary interface. |

These are bounded form-level tasks, not complete instruction families. In
particular, `.b64` bit counts still produce a **32-bit destination**. Do not
infer source and destination widths from a single shared width parameter.
The 64-bit register bank currently has address-oriented names; reusing or
reorganizing it for general integer operations needs an explicit interface
decision before dispatching those forms.

## First task: precise contract

The worker may change `Ptx/Scalar.lean` and `Ptx/ScalarText.lean`, and add
`Ptx/IntegerMinMax.lean`. The coordinator maintains imports, the dependency audit,
coverage records, and Stratic links. The worker must not replace the foundations
or change existing theorem statements to make the task easier.

**Values.** For every pair of 32-bit words `a` and `b`, interpreting the words as
unsigned natural numbers, the result of minimum is their mathematical minimum
and the result of maximum is their mathematical maximum. Each operation returns
one of the two supplied words. The instruction sections specify comparisons,
not an arithmetic subtraction whose wrapped result determines ordering.
All bit patterns are covered; there is no overflow premise or exceptional input.
Equal inputs return their common bit pattern. The manual's chosen branch on a
tie has no observable distinction for these unsigned words.

**Instruction execution.** Add two binary-operation cases that use the existing
operands, register state, guards, and execution machinery. When the guard is
true, read both operands from the input state, write the selected value to the
destination, and advance the program counter by one. Reading must precede the
write even when the destination is also a source register. Other word registers,
address registers, predicates, and memory are unchanged. There is no memory
event. Direct register-read/write metadata must remain correct. When the guard
is false, the destination is unchanged and only the usual skipped-instruction
behavior occurs. This preserves the existing model's restrictions; it does not
establish a new general PTX dependency or concurrency semantics.

[§9.7.1](../../references/nvidia/ptx-isa-9.4/index.html#integer-arithmetic-instructions)
permits register and immediate integer operands.
[§6.1](../../references/nvidia/ptx-isa-9.4/index.html#operand-type-information)
explains compatible operand types, and
[§6.3](../../references/nvidia/ptx-isa-9.4/index.html#destination-operands)
requires the destination in register storage.
[§9.3](../../references/nvidia/ptx-isa-9.4/index.html#predicated-execution)
gives positive and negated predicate guards. The existing typed operand boundary
represents 32-bit values without checking source-file register declarations;
this task must retain that limitation rather than claim a complete parser.

**Typed text boundary.** Decode the exact two mnemonics with a word-register
destination and two word operands; register and immediate sources are allowed.
Encode them canonically and preserve the existing guarded round-trip theorem.
Reject an immediate destination, missing or extra operands, and wrong operand
categories. The current decoder distinguishes unsupported mnemonics from invalid
operands for a supported mnemonic; both cases must remain distinct.

**Required proof content.** Require universal unsigned-value characterizations
for both operations, operand membership, commutativity, idempotence, and unsigned
bounds on the result. These facts must refer to the actual `BinOp.eval` cases,
not unrelated helper functions. At least one general execution theorem should
connect the operation to the destination value for arbitrary input states and
operands with a true guard. Frame facts (which state components remain unchanged),
false-guard behavior, and source/destination overlap must be covered by the
existing reusable rules or new proved statements. Verify which existing results
supply them rather than silently counting them as proved. Existing text round
trip and supported-decode results must still build for the expanded operation
type. Inspect theorem dependencies; no `sorry`, new unchecked axioms, or premises
that merely assume the desired result are acceptable.

The numerical characterizations are exact finite-integer equalities, not
floating-point error bounds. A proof of commutativity or operand membership alone
would not distinguish minimum from maximum, or signed from unsigned comparison.

## Independently prepared distinguishing examples

Expected values below come from unsigned ordering, before inspecting any worker
implementation. Hexadecimal notation denotes the 32-bit pattern.

| Inputs `(a, b)` | `min.u32` | `max.u32` | Purpose |
| --- | --- | --- | --- |
| `(0, 0)` | `0` | `0` | Tie at zero |
| `(7, 11)` and `(11, 7)` | `7` | `11` | Both operand orders |
| `(0xffffffff, 0)` | `0` | `0xffffffff` | Signed comparison would reverse the result |
| `(0x80000000, 0x7fffffff)` | `0x7fffffff` | `0x80000000` | Across the signed/unsigned boundary |
| `(0xffffffff, 0xffffffff)` | `0xffffffff` | `0xffffffff` | Equal maximum values |

Also execute a case with destination equal to the left source and another equal
to the right source; a false positive guard and a false negated guard must leave
the destination unchanged. Include register/immediate mixtures in text checks.
Try `min.relu.u32`, `max.s32`, `min.u64`, and `max.u16x2`: none is part of this
assignment. A correct rejection means unsupported **by this implementation**;
for example `max.s32` is legal PTX and must not be described as illegal PTX.

For review-process evaluation, useful deliberately wrong candidates are swapped
minimum/maximum, signed comparison, and a decoder that accepts `.relu.u32` as an
alias. The first two can still have many correct algebraic proofs. A failed
mutation check diagnoses a review gap; detecting these examples is not proof
that the reviewer catches all possible errors.

## Excluded forms and source cautions

The min/max sections also cover scalar `.u16`, `.u64`, `.s16`, `.s32`, `.s64`,
and packed `.u16x2`, `.s16x2`, `.u8x4`, `.s8x4` forms. Packed forms apply the
operation independently within each smaller component. `.relu` clamps negative
results to zero and is specified only for `.s32`, `.s16x2`, and `.s8x4`, not
`.u32`. The newer forms have separate version and hardware-family restrictions.
All remain visibly unimplemented after the first task.

The pinned source's `min` example places `.relu` after `.s16x2`, whereas its
syntax template places `.relu` before the type. The `neg.s8x4` example has three
operands although its syntax and semantics describe a unary operation. Neither
inconsistency affects the selected unsigned forms. Do not resolve them by
silently accepting arbitrary modifier order or arity when those forms are later
assigned.

Signed `abs`/`neg` are deferred: the first interface is unsigned and the exact
minimum-signed-integer case deserves an explicit source-derived interpretation
before assignment. A worker must not replace finite-width behavior with
unbounded mathematical absolute value or avoid that input through an assumption.

## Foundation review result

`Word` is `BitVec 32`; `Operand32`, unsigned `Compare.eval`, and binary execution
already provide the necessary value and state representations for the selected
min/max forms. Inspection found no mismatch that blocks this task. This was a
focused review, not revalidation of every existing instruction.

`ScalarText` is explicitly a typed mnemonic boundary, not a complete PTX parser.
The environment's current eligibility checker concerns selected memory forms;
it is not a universal arithmetic-instruction version/target validator. The
first task's PTX 1.0/all-target condition must be recorded in coverage evidence,
without claiming that the existing memory checker establishes it. Later bit-count
and reversal tasks need their PTX 2.0/`sm_20` requirements represented before
claiming executable target validation. Pure value functions alone would be a
smaller, clearly labeled result than integrated instruction coverage.
