# shf fixed worker contract

Implement ONLY `Ptx/Shf32.lean`, namespace `Ptx.Scalar.Shf32`.
Use the existing Pure32 execution and ScalarText interfaces. No shared-file edits.

Selected spellings: shf.l.clamp.b32, shf.l.wrap.b32, shf.r.clamp.b32, shf.r.wrap.b32.
Operation constructors correspond in that order.
Pinned PTX 9.4 source: `.ptx-source/9.4/index.html`, SHA-256
`0aa31c15735a30b5d7c0fa1fe02570dcd37fe80800afca74bcc96c9132b81fed`.
Read anchors logic-and-shift-instructions-shf, plus predicated-execution,
instruction-statements, operand-type-information, source-operands,
destination-operands, integer-constants and type-information-for-instructions-and-operands.

The first word a is the LOW half and the second word b is the HIGH half of a
64-bit concatenation. Left funnel shift returns the HIGH 32 bits of the shifted
concatenation; right funnel shift returns the LOW 32 bits. The control is an
unsigned 32-bit count: clamp uses min(c,32), wrap uses c modulo 32. Count 32 in
clamp mode returns a for left and b for right; wrap count 32 acts like zero.
All four selected forms were introduced in PTX 3.1 and require SM32 or higher.
The four equations below use zero-filling BitVec shifts by Nat amounts, which
produce zero at count 32. They prescribe results, not an implementation body.

The exact slice is ISA 94 and numeric SM >= 32; this is a feature
threshold, not target-name validation. All input words and source/destination
aliases are allowed. Operands are read from the incoming state. Both guard
polarities are supported; skips advance only PC and record only the guard read.
Target restrictions apply even to skips. Enabled syntactic reads preserve source
order and repeats. Memory, address registers, predicates and other value registers
are preserved. No extra preconditions or new axioms.

Sources and destination are compatible declared 32-bit values; immediate words
are already decoded and size-converted. Register declaration validation, raw text,
other widths/options and hardware correspondence are outside the slice.

Use the following interface and exact universal theorem statements. Derive the
computation body yourself from the pinned source; no body or algorithm is prescribed.
The four result equations describe the required words for all input values, independently
of your chosen implementation. Definitions for common execution plumbing are supplied. Text.encode uses a word-register destination and the word sources in
field order, preserving the guard. Each operation has exactly its listed spelling.
Text.encode emits the destination register followed by three word operands (first,
second, control); all three can be registers or already converted immediates.
Text.decode accepts exactly these encodings, distinguishes recognized malformed
operands (invalidOperands) from all other names (unsupportedMnemonic).

```lean
def SupportedTarget (target : Ptx.Target) : Prop := target.isa = 94 ∧ 32 ≤ target.sm

inductive Operation where
  | leftClamp | leftWrap | rightClamp | rightWrap
  deriving DecidableEq, Repr

structure Instr where
  guard : Scalar.Guard := .always
  operation : Operation
  destination : Nat
  first : Scalar.Operand32
  second : Scalar.Operand32
  control : Scalar.Operand32
  deriving DecidableEq, Repr

def compute (op : Operation) (a b c : Word) : Word

def family : Pure32.Family Operation :=
  Pure32.Family.ofFunction (fun _ => 3) (fun _ => 0)
    (fun op words _ => compute op (words 0) (words 1) (words 2))
    (fun target _ => SupportedTarget target)

def lower (i : Instr) : Pure32.Instr family where
  guard := i.guard
  operation := i.operation
  destination := i.destination
  words := fun j => if j.val = 0 then i.first else if j.val = 1 then i.second else i.control
  predicates := Fin.elim0

def result (i : Instr) (s : Scalar.State) : Word :=
  compute i.operation (i.first.eval s) (i.second.eval s) (i.control.eval s)

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

theorem compute_leftClamp (a b c : Word) :
    compute .leftClamp a b c = (b <<< (min c.toNat 32)) ||| (a >>> (32 - (min c.toNat 32)))

theorem compute_leftWrap (a b c : Word) :
    compute .leftWrap a b c = (b <<< (c.toNat % 32)) ||| (a >>> (32 - (c.toNat % 32)))

theorem compute_rightClamp (a b c : Word) :
    compute .rightClamp a b c = (b <<< (32 - (min c.toNat 32))) ||| (a >>> (min c.toNat 32))

theorem compute_rightWrap (a b c : Word) :
    compute .rightWrap a b c = (b <<< (32 - (c.toNat % 32))) ||| (a >>> (c.toNat % 32))


theorem results_iff (op : Operation) (words : Fin 3 → Word) (predicates : Fin 0 → Bool) (value : Word) :
    family.Results op words predicates value ↔ value = compute op (words 0) (words 1) (words 2)

theorem lower_operation (i : Instr) : (lower i).operation = i.operation

theorem lower_fields (i : Instr) :
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words (⟨0, by decide⟩ : Fin 3) = i.first ∧ (lower i).words (⟨1, by decide⟩ : Fin 3) = i.second ∧ (lower i).words (⟨2, by decide⟩ : Fin 3) = i.control

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

Run `lake build Ptx.Shf32` and `lake env lean formalization/checks/shf-v1.lean`. Audit public definitions and proofs with #print axioms. Only standard propext, Classical.choice, Quot.sound allowed. No sorry/admit, new axioms, native_decide, commits, extra model calls, or changes to the checkers, contracts, descriptions or foundations. Use existing leaf modules as templates. Report exact blockers; do not weaken the contract.

The existing Ptx.BitVecProof module and its examples/bitvector_proofs.lean and
docs/formalization/bitvector-proofs.md guide are available unchanged. No new
instruction-specific proof hints or computation body are supplied in this first
invocation. Derive and prove your implementation under the fixed output laws.
Do not inspect private coordinator fixtures or unrelated archived trial fixtures.
