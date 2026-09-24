# mulhi32 fixed worker contract

Implement ONLY `Ptx/MulHi32.lean`, namespace `Ptx.Scalar.MulHi32`.
Use the existing Pure32 execution and ScalarText interfaces. No shared-file edits.

Selected spellings: mul.hi.u32, mul.hi.s32.
Pinned PTX 9.4 source: `.ptx-source/9.4/index.html`, SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
Read anchors integer-arithmetic-instructions-mul, plus predicated-execution,
instruction-statements, operand-type-information, source-operands,
destination-operands, integer-constants and type-information-for-instructions-and-operands.

Return the upper 32 bits of the full 64-bit product. Unsigned operands use values 0 through 2^32-1; signed operands use two-complement values. Signed division by positive 2^32 is floor division, including negative products. No saturation or extra range assumptions. Introduced in PTX 1.0; all target architectures (numeric feature floor sm_10).

The exact slice is ISA 94 and numeric SM >= 10; this is a feature
threshold, not target-name validation. All input words and source/destination
aliases are allowed. Operands are read from the incoming state. Both guard
polarities are supported; skips advance only PC and record only the guard read.
Target restrictions apply even to skips. Enabled syntactic reads preserve source
order and repeats. Memory, address registers, predicates and other value registers
are preserved. No extra preconditions or new axioms.

Sources and destination are compatible declared 32-bit values; immediate words
are already decoded and size-converted. Register declaration validation, raw text,
other widths/options and hardware correspondence are outside the slice.

Use these definitions and exact universal theorem statements. Their proofs are
your task. Text.encode uses a word-register destination and the word sources in
field order, preserving the guard. Each operation has exactly its listed spelling.
Text.decode accepts exactly these encodings, distinguishes recognized malformed
operands (invalidOperands) from all other names (unsupportedMnemonic).

```lean
def SupportedTarget (target : Ptx.Target) : Prop := target.isa = 94 ∧ 10 ≤ target.sm

inductive Operation where
  | unsigned | signed
  deriving DecidableEq, Repr

structure Instr where
  guard : Scalar.Guard := .always
  operation : Operation
  destination : Nat
  left : Scalar.Operand32
  right : Scalar.Operand32
  deriving DecidableEq, Repr

def compute (op : Operation) (a b : Word) : Word :=
    match op with
      | .unsigned => BitVec.ofNat 32 ((a.toNat * b.toNat) / 2^32)
      | .signed => BitVec.ofInt 32 ((a.toInt * b.toInt) / (2^32 : Int))

def family : Pure32.Family Operation :=
  Pure32.Family.ofFunction (fun _ => 2) (fun _ => 0)
    (fun op words _ => compute op (words 0) (words 1))
    (fun target _ => SupportedTarget target)

def lower (i : Instr) : Pure32.Instr family where
  guard := i.guard
  operation := i.operation
  destination := i.destination
  words := fun j => if j.val = 0 then i.left else i.right
  predicates := Fin.elim0

def result (i : Instr) (s : Scalar.State) : Word :=
  compute i.operation (i.left.eval s) (i.right.eval s)

abbrev Occurrence := Pure32.Occurrence family
abbrev Eval (i : Instr) := Pure32.Eval (lower i)
abbrev Step (target : Ptx.Target) (program : List Instr) := Pure32.Step target (program.map lower)

def occurrence (s : Scalar.State) (i : Instr) (executed : Bool) : Occurrence :=
  Pure32.occurrence s (lower i) executed

namespace Text
  def supportedMnemonic : String → Bool
  def encode : Instr → Scalar.Text.Statement
  def decode : Scalar.Text.Statement → Except Scalar.Text.DecodeError Instr
end Text

theorem compute_eq (op : Operation) (a b : Word) :
    compute op a b = (match op with
      | .unsigned => BitVec.ofNat 32 ((a.toNat * b.toNat) / 2^32)
      | .signed => BitVec.ofInt 32 ((a.toInt * b.toInt) / (2^32 : Int)))

theorem results_iff (op : Operation) (words : Fin 2 → Word) (predicates : Fin 0 → Bool) (value : Word) :
    family.Results op words predicates value ↔ value = compute op (words 0) (words 1)

theorem lower_operation (i : Instr) : (lower i).operation = i.operation

theorem lower_fields (i : Instr) :
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words (⟨0, by decide⟩ : Fin 2) = i.left ∧ (lower i).words (⟨1, by decide⟩ : Fin 2) = i.right

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
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds

theorem eval_other (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (evaluated : Eval i s next event) (different : other ≠ i.destination) :
    next.regs other = s.regs other

theorem eval_event (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) :
    event = occurrence s i (i.guard.eval s)

theorem eval_deterministic (i : Instr) (s next₁ next₂ : Scalar.State) (event₁ event₂ : Occurrence)
    (left : Eval i s next₁ event₁) (right : Eval i s next₂ event₂) :
    next₁ = next₂ ∧ event₁ = event₂

theorem eval_exists (i : Instr) (s : Scalar.State) : ∃ next event, Eval i s next event

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

theorem Text.decode_encode (i : Instr) : Text.decode (Text.encode i) = .ok i

theorem Text.decode_iff (statement : Scalar.Text.Statement) (i : Instr) :
    Text.decode statement = .ok i ↔ statement = Text.encode i
```

Run `lake build Ptx.MulHi32` and `lake env lean formalization/checks/mulhi32-v1.lean`. Audit public definitions and proofs with #print axioms. Only standard propext, Classical.choice, Quot.sound allowed. No sorry/admit, new axioms, native_decide, commits, extra model calls, or changes to the checkers, contracts, descriptions or foundations. Use existing leaf modules as templates. Report exact blockers; do not weaken the contract.
