# Frozen signed-minmax32-v1 worker contract

Implement only `Ptx/SignedMinMax32.lean`, namespace `Ptx.Scalar.SignedMinMax32`.
All other source, package files, checks, descriptions and toolchain pins are
immutable. This is a leaf of the shared `Ptx.Scalar.Pure32` mechanism, not a new
execution engine. Import `Ptx.Pure32` and `Ptx.ScalarText`. No changes to Scalar,
Pure32, shared Text, root imports or the Lake configuration are allowed.

## Source and precise slice

Use pinned PTX ISA9.4 `references/nvidia/ptx-isa-9.4/index.html`, SHA256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
§9.7.1.13 `integer-arithmetic-instructions-min` and §9.7.1.14
`integer-arithmetic-instructions-max` explicitly distinguish signed and unsigned
comparisons. Both selected scalar .s32 forms were introduced in PTX1.0 and are
supported on all target architectures. The .relu and packed forms carry other
restrictions and are outside this contract. `BitVec.toInt` supplies the exact
32-bit two's-complement interpretation, including −2147483648 and −1. No range,
nonnegative, nonoverflow, or unequal-source premise may exclude a bit pattern.

Also inspect §9.3 `predicated-execution`, §4.3.2 `instruction-statements`,
§6.1 `operand-type-information`, §6.2 `source-operands`, §6.3
`destination-operands`, §4.5.1 `integer-constants`, and §9.4
`type-information-for-instructions-and-operands`. Word-register sources and destinations represent compatible declared
32-bit registers; register declaration/type checking is outside this typed layer.
Integer constants in the source are initially 64-bit and converted at use;
immediate words here are already decoded and size-converted 32-bit integer/bits values, not raw text
or arbitrary numeric conversions. Preserve all source bits. The scalar state
supplies every incoming register value; no uninitialized-register analysis is
claimed. Instruction guards are `.always` or `.pred index positive` and permit
both polarities independently of the operation's operands.

Only `min.s32` and `max.s32` is/are accepted. The numeric target slice is
`target.isa = 94 ∧ 10 ≤ target.sm`. The source introduction date motivates the
feature floor, but this predicate is not validation of a real declared target
spelling nor a claim about current assembler acceptance of historical targets.
It intentionally does not accept other PTX ISA versions or interpret a/f suffixes.

## Frozen representation

Private helpers/proof methods may vary, but the following public API and its
meaning are fixed. Every declaration shown without a body must be implemented.
Use the existing `Ptx.Word`, `Scalar.State`, `Operand32`, `Guard`, and `Register`.

```lean
namespace Ptx.Scalar.SignedMinMax32
def SupportedTarget (target : Ptx.Target) : Prop :=
  target.isa = 94 ∧ 10 ≤ target.sm
inductive Operation where
  | min | max
  deriving DecidableEq, Repr
structure Instr where
  guard : Scalar.Guard := .always
  operation : Operation
  destination : Nat
  left : Scalar.Operand32
  right : Scalar.Operand32
  deriving DecidableEq, Repr
-- Comparison is signed, and the result copies an unchanged source word.
def compute (op : Operation) (a b : Word) : Word
-- .min => if a.toInt < b.toInt then a else b
-- .max => if a.toInt > b.toInt then a else b
-- wordArity := fun _ => 2; predicateArity := fun _ => 0.
-- family = Pure32.Family.ofFunction ...
--   (fun op words _ => compute op (words 0) (words 1))
--   (fun target _ => SupportedTarget target).
def family : Pure32.Family Operation
-- lower preserves i.operation and has no predicate arguments (Fin 0).
def lower (i : Instr) : Pure32.Instr family
def result (i : Instr) (s : Scalar.State) : Word :=
  compute i.operation (i.left.eval s) (i.right.eval s)

abbrev Occurrence := Pure32.Occurrence family
abbrev Eval (i : Instr) := Pure32.Eval (lower i)
abbrev Step (target : Ptx.Target) (program : List Instr) :=
  Pure32.Step target (program.map lower)
def occurrence (s : Scalar.State) (i : Instr) (executed : Bool) : Occurrence :=
  Pure32.occurrence s (lower i) executed
namespace Text
  def supportedMnemonic : String → Bool
  def encode (i : Instr) : Scalar.Text.Statement
  def decode (statement : Scalar.Text.Statement) : Except Scalar.Text.DecodeError Instr
end Text
end Ptx.Scalar.SignedMinMax32
```

`lower` preserves guard/destination and maps word argument0 to left, argument1
to right. Its predicate arguments/operation are exactly specified above. Do not
copy the shared inductive Eval or Step. Occurrences contain the actual lowered
family instruction fetched from the lowered program, not a fabricated integer
opcode. Since the leaf is lowered, `step_origin` must also recover the exact
original leaf at the original program counter.

The typed encoder uses exactly [.word (.reg destination), .word left, .word right], the original guard,
and the exact mnemonic associated with its operation. The decoder must invert
that format. `supportedMnemonic` is true exactly for the listed spellings.
A recognized mnemonic with malformed operands (including an immediate
DESTINATION, missing/extra operand, wrong token category) returns
`.error (.invalidOperands statement.mnemonic)`. Any other spelling returns
`.error (.unsupportedMnemonic statement.mnemonic)`, even with malformed operands.
No raw-string parser, literal evaluator or implicit qualifier expansion is required.

## Required universal theorems

These signatures are frozen. No strengthened hypotheses, excluded aliases or
excluded input words. Derivation from shared proofs is encouraged. `result` is
computed from incoming operands before destination writes. The lower-fields
and semantic result proofs together must cover sources naming the destination.
Keep both conditional branches in syntactic read metadata, preserving repeats;
these are direct operand reads, not a PTX semantic-dependency/NTA claim.

```lean
namespace Ptx.Scalar.SignedMinMax32
theorem compute_min (a b : Word) :
    compute .min a b = if a.toInt < b.toInt then a else b

theorem compute_max (a b : Word) :
    compute .max a b = if a.toInt > b.toInt then a else b

theorem compute_toInt (op : Operation) (a b : Word) :
    (compute op a b).toInt = match op with
      | .min => min a.toInt b.toInt
      | .max => max a.toInt b.toInt

theorem results_iff (op : Operation) (words : Fin 2 → Word) (predicates : Fin 0 → Bool) (value : Word) :
    family.Results op words predicates value ↔ value = compute op (words 0) (words 1)

theorem lower_operation (i : Instr) :
    (lower i).operation = i.operation

theorem lower_fields (i : Instr) :
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words 0 = i.left ∧ (lower i).words 1 = i.right

theorem eval_true_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true) :
    Eval i s next event ↔
      next = Pure32.write s i.destination (result i s) ∧ event = occurrence s i true

theorem eval_false_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false) :
    Eval i s next event ↔
      next = {s with pc := s.pc + 1} ∧ event = occurrence s i false

theorem eval_destination (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) (enabled : i.guard.eval s = true) :
    next.regs i.destination = result i s

theorem eval_frame (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) :
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧
      next.addrs = s.addrs ∧ next.preds = s.preds

theorem eval_other (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (evaluated : Eval i s next event) (different : other ≠ i.destination) :
    next.regs other = s.regs other

theorem eval_event (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) :
    event = occurrence s i (i.guard.eval s)

theorem eval_deterministic (i : Instr) (s next₁ next₂ : Scalar.State) (event₁ event₂ : Occurrence)
    (left : Eval i s next₁ event₁) (right : Eval i s next₂ event₂) :
    next₁ = next₂ ∧ event₁ = event₂

theorem eval_exists (i : Instr) (s : Scalar.State) :
    ∃ next event, Eval i s next event

theorem step_origin (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (stepped : Step target program s next event) :
    SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧
      event.pc = s.pc ∧ event.instruction = lower i ∧ Eval i s next event

theorem step_exists (target : Ptx.Target) (program : List Instr) (s : Scalar.State) (i : Instr)
    (supported : SupportedTarget target) (fetch : program[s.pc]? = some i) :
    ∃ next event, Step target program s next event

theorem step_no_fetch (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (missing : program[s.pc]? = none) :
    ¬ Step target program s next event

theorem step_unsupported_target (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (unsupported : ¬ SupportedTarget target) :
    ¬ Step target program s next event

theorem Text.decode_encode (i : Instr) :
    Text.decode (Text.encode i) = .ok i

theorem Text.decode_iff (statement : Scalar.Text.Statement) (i : Instr) :
    Text.decode statement = .ok i ↔ statement = Text.encode i
end Ptx.Scalar.SignedMinMax32
```

Every enabled transition changes exactly destination and PC; every skip changes
only PC and has guard-only read metadata, no writes, no memory effect. Existence
is for all supplied states and bit patterns. Target checks apply to fetched
steps even on false guards. No fetch is not a modeled kernel halt. There is no
whole-program runner, termination, memory-order or hardware-conformance claim.

## Completion and independent acceptance

Run `lake build Ptx.SignedMinMax32` and `lake env lean Ptx/SignedMinMax32.lean` from the root.
Inspect dependencies of all public proof declarations with `#print axioms`.
Only `propext`, `Classical.choice`, `Quot.sound` may appear. No `sorry`, `admit`,
new axioms or `native_decide`; no external inference calls or commits.
The coordinator owns the frozen independent driver
`formalization/checks/signed-minmax32-v1.lean`, source review and final acceptance.
The driver checks source-specific outcomes separately from mutually consistent
encode/decode proofs, and covers both guards, nonzero-PC fetch, aliasing,
repeated reads, target exclusion and malformed/unsupported spellings.
Do not edit it or specialize definitions to its examples. Report exact remaining
obligations if blocked, rather than weaken the contract. Leaf coverage remains
unaccepted until the coordinator completes independent checks and source review.
