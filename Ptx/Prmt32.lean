import Ptx.Pure32
import Ptx.ScalarText
import Ptx.BitVecProof

namespace Ptx.Scalar.Prmt32

open Pure32

private def w0 : Fin 3 := ⟨0, by decide⟩
private def w1 : Fin 3 := ⟨1, by decide⟩
private def w2 : Fin 3 := ⟨2, by decide⟩

def SupportedTarget (target : Ptx.Target) : Prop := target.isa = 94 ∧ 20 ≤ target.sm

inductive Operation where
  | permute
  deriving DecidableEq, Repr

structure Instr where
  guard : Scalar.Guard := .always
  operation : Operation
  destination : Nat
  first : Scalar.Operand32
  second : Scalar.Operand32
  control : Scalar.Operand32
  deriving DecidableEq, Repr

def compute (_op : Operation) (a b c : Word) : Word :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 32 =>
    let selector := (c.toNat / 2 ^ (4 * (i.val / 8))) % 16
    let source := if selector % 8 < 4 then a else b
    source.getLsbD (8 * (selector % 4) + (if 8 ≤ selector then 7 else i.val % 8)))).cast (by simp)

def family : Pure32.Family Operation :=
  Pure32.Family.ofFunction (fun _ => 3) (fun _ => 0)
    (fun op words _ => compute op (words w0) (words w1) (words w2))
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

theorem compute_bit (op : Operation) (a b c : Word) (bit : Nat) (bound : bit < 32) :
    (compute op a b c).getLsbD bit = (let selector := (c.toNat / 2 ^ (4 * (bit / 8))) % 16
     let source := if selector % 8 < 4 then a else b
     source.getLsbD (8 * (selector % 4) + (if 8 ≤ selector then 7 else bit % 8))) := by
  cases op
  simp only [compute, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [bound]

theorem results_iff (op : Operation) (words : Fin 3 → Word) (predicates : Fin 0 → Bool) (value : Word) :
    family.Results op words predicates value ↔ value = compute op (words 0) (words 1) (words 2) := by
  simp [family, Pure32.Family.ofFunction, compute, w0, w1, w2]

theorem lower_operation (i : Instr) : (lower i).operation = i.operation := rfl

theorem lower_fields (i : Instr) :
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words (⟨0, by decide⟩ : Fin 3) = i.first ∧ (lower i).words (⟨1, by decide⟩ : Fin 3) = i.second ∧ (lower i).words (⟨2, by decide⟩ : Fin 3) = i.control := by
  simp [lower]

theorem eval_true_iff (i : Instr) (s next : Scalar.State) (event : Occurrence) (enabled : i.guard.eval s = true) :
    Eval i s next event ↔ next = Pure32.write s i.destination (result i s) ∧ event = occurrence s i true := by
  change Pure32.Eval (lower i) s next event ↔ _
  rw [Pure32.eval_true_iff (lower i) s next event enabled]
  constructor
  · rintro ⟨value, h, hn, he⟩
    have hv : value = result i s := by
      simpa [family, Pure32.Family.ofFunction, Pure32.Instr.wordValues, Pure32.Instr.predicateValues, lower, result, w0, w1, w2] using h
    subst value
    exact ⟨hn, he⟩
  · rintro ⟨hn, he⟩
    refine ⟨result i s, ?_, hn, he⟩
    simp [family, Pure32.Family.ofFunction, Pure32.Instr.wordValues, lower, result, w0, w1, w2]

theorem eval_false_iff (i : Instr) (s next : Scalar.State) (event : Occurrence) (disabled : i.guard.eval s = false) :
    Eval i s next event ↔ next = {s with pc := s.pc + 1} ∧ event = occurrence s i false :=
  Pure32.eval_false_iff (lower i) s next event disabled

theorem eval_destination (i : Instr) (s next : Scalar.State) (event : Occurrence) (evaluated : Eval i s next event) (enabled : i.guard.eval s = true) :
    next.regs i.destination = result i s := by
  rcases (eval_true_iff i s next event enabled).mp evaluated with ⟨rfl, _⟩
  simp [Pure32.write]

theorem eval_frame (i : Instr) (s next : Scalar.State) (event : Occurrence) (evaluated : Eval i s next event) :
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds := Pure32.eval_frame evaluated

theorem eval_other (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat) (evaluated : Eval i s next event) (different : other ≠ i.destination) : next.regs other = s.regs other := Pure32.eval_other evaluated different

theorem eval_event (i : Instr) (s next : Scalar.State) (event : Occurrence) (evaluated : Eval i s next event) : event = occurrence s i (i.guard.eval s) := by
  simpa [occurrence, lower] using Pure32.eval_event evaluated

theorem eval_deterministic (i : Instr) (s next₁ next₂ : Scalar.State) (event₁ event₂ : Occurrence) (left : Eval i s next₁ event₁) (right : Eval i s next₂ event₂) : next₁ = next₂ ∧ event₁ = event₂ := by
  apply Pure32.eval_deterministic (i := lower i) (left := left) (right := right)
  intro words predicates a b ha hb
  exact ha.trans hb.symm

theorem eval_exists (i : Instr) (s : Scalar.State) : ∃ next event, Eval i s next event := Pure32.eval_exists (lower i) s

theorem step_origin (target : Ptx.Target) (program : List Instr) (s next : Scalar.State) (event : Occurrence) (stepped : Step target program s next event) :
    SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧ event.pc = s.pc ∧ event.instruction = lower i ∧ Eval i s next event := by
  obtain ⟨j, fetch, supported, pc, ins, evaluated⟩ := Pure32.step_origin stepped
  have original : ∃ i, program[s.pc]? = some i ∧ lower i = j := by
    cases hx : program[s.pc]? with
    | none => simp [hx] at fetch
    | some i => have hm : some (lower i) = some j := by simpa [hx] using fetch
                exact ⟨i, by simp, Option.some.inj hm⟩
  obtain ⟨i, fi, eq⟩ := original
  have ev : Eval i s next event := Eq.mp (congrArg (fun x : Pure32.Instr family => Pure32.Eval x s next event) eq.symm) evaluated
  exact ⟨supported, i, fi, pc, ins.trans eq.symm, ev⟩

theorem step_exists (target : Ptx.Target) (program : List Instr) (s : Scalar.State) (i : Instr) (supported : SupportedTarget target) (fetch : program[s.pc]? = some i) : ∃ next event, Step target program s next event := by
  have mapped : (program.map lower)[s.pc]? = some (lower i) := by simp [fetch]
  exact Pure32.step_exists (lower i) mapped supported

theorem step_no_fetch (target : Ptx.Target) (program : List Instr) (s next : Scalar.State) (event : Occurrence) (missing : program[s.pc]? = none) : ¬ Step target program s next event := by
  exact Pure32.step_no_fetch (program := program.map lower) (s := s) (by simpa using missing)

theorem step_unsupported_target (target : Ptx.Target) (program : List Instr) (s next : Scalar.State) (event : Occurrence) (unsupported : ¬ SupportedTarget target) : ¬ Step target program s next event := by
  intro h
  obtain ⟨_, _, admitted, _⟩ := h
  exact unsupported admitted

namespace Text

def supportedMnemonic (mnemonic : String) : Bool := mnemonic == "prmt.b32"

def encode (i : Instr) : Scalar.Text.Statement :=
  ⟨i.guard, "prmt.b32", [.word (.reg i.destination), .word i.first, .word i.second, .word i.control]⟩

def decode (statement : Scalar.Text.Statement) : Except Scalar.Text.DecodeError Instr :=
  if supportedMnemonic statement.mnemonic then
    match statement.operands with
    | [.word (.reg d), .word a, .word b, .word c] => .ok ⟨statement.guard, .permute, d, a, b, c⟩
    | _ => .error (.invalidOperands statement.mnemonic)
  else .error (.unsupportedMnemonic statement.mnemonic)

theorem decode_encode (i : Instr) : decode (encode i) = .ok i := by
  cases i with | mk guard operation destination first second control => cases operation <;> rfl

theorem decode_iff (statement : Scalar.Text.Statement) (i : Instr) : decode statement = .ok i ↔ statement = encode i := by
  constructor
  · intro h
    rcases statement with ⟨guard, mnemonic, operands⟩
    cases i with
    | mk g op d a b c =>
      cases op
      unfold decode at h
      by_cases hm : mnemonic = "prmt.b32"
      · subst mnemonic
        simp [supportedMnemonic] at h
        split at h
        · injection h with hi
          cases hi
          rfl
        · simp at h
      · simp [supportedMnemonic, hm] at h
  · intro h
    subst statement
    exact decode_encode i

end Text
end Ptx.Scalar.Prmt32
