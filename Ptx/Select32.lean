import Ptx.Pure32
import Ptx.ScalarText

namespace Ptx.Scalar.Select32

open Pure32

private def w0 : Fin 2 := ⟨0, by decide⟩
private def w1 : Fin 2 := ⟨1, by decide⟩
private def p0 : Fin 1 := ⟨0, by decide⟩

def SupportedTarget (target : Ptx.Target) : Prop :=
  target.isa = 94 ∧ 10 ≤ target.sm

inductive Operation where
  | selp
  deriving DecidableEq, Repr

structure Instr where
  guard : Scalar.Guard := .always
  destination : Nat
  left : Scalar.Operand32
  right : Scalar.Operand32
  predicate : Nat
  deriving DecidableEq, Repr

def compute (a b : Word) (c : Bool) : Word := if c then a else b

def family : Pure32.Family Operation :=
  Pure32.Family.ofFunction (fun _ => 2) (fun _ => 1)
    (fun _ words predicates => compute (words w0) (words w1) (predicates p0))
    (fun target _ => SupportedTarget target)

def lower (i : Instr) : Pure32.Instr family :=
  ⟨i.guard, .selp, i.destination,
    fun index => if index.val = 0 then i.left else i.right,
    fun _ => .reg i.predicate true⟩

def result (i : Instr) (s : Scalar.State) : Word :=
  compute (i.left.eval s) (i.right.eval s) (s.preds i.predicate)

abbrev Occurrence := Pure32.Occurrence family
abbrev Eval (i : Instr) := Pure32.Eval (lower i)
abbrev Step (target : Ptx.Target) (program : List Instr) :=
  Pure32.Step target (program.map lower)

def occurrence (s : Scalar.State) (i : Instr) (executed : Bool) : Occurrence :=
  Pure32.occurrence s (lower i) executed

theorem compute_eq (a b : Word) (c : Bool) :
    compute a b c = if c then a else b := rfl

theorem results_iff (op : Operation) (words : Fin 2 → Word) (predicates : Fin 1 → Bool) (value : Word) :
    family.Results op words predicates value ↔ value = if predicates p0 then words w0 else words w1 := by
  cases op
  rfl

theorem lower_predicate (i : Instr) :
    (lower i).operation = .selp ∧ (lower i).predicates p0 = .reg i.predicate true := by
  simp [lower]

theorem lower_fields (i : Instr) :
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words w0 = i.left ∧ (lower i).words w1 = i.right := by
  simp [lower, w0, w1]

theorem eval_true_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true) :
    Eval i s next event ↔
      next = Pure32.write s i.destination (result i s) ∧ event = occurrence s i true := by
  change Pure32.Eval (lower i) s next event ↔ _
  rw [Pure32.eval_true_iff (lower i) s next event (by simpa [lower] using enabled)]
  constructor
  · rintro ⟨value, h, hn, he⟩
    have hv : value = result i s := by
      simpa [Pure32.Instr.wordValues, Pure32.Instr.predicateValues, lower, result, w0, w1, p0,
        family, Pure32.Family.ofFunction] using h
    subst value
    exact ⟨by simpa [lower, family, Pure32.Family.ofFunction,
      Pure32.Instr.wordValues, Pure32.Instr.predicateValues, w0, w1, p0, result] using hn, he⟩
  · rintro ⟨hn, he⟩
    refine ⟨result i s, ?_, hn, he⟩
    simpa [Pure32.Instr.wordValues, Pure32.Instr.predicateValues, lower, result, w0, w1, p0,
      family, Pure32.Family.ofFunction]

theorem eval_false_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false) :
    Eval i s next event ↔
      next = {s with pc := s.pc + 1} ∧ event = occurrence s i false := by
  change Pure32.Eval (lower i) s next event ↔ _
  exact Pure32.eval_false_iff (lower i) s next event (by simpa [lower] using disabled)

theorem eval_destination (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) (enabled : i.guard.eval s = true) :
    next.regs i.destination = result i s := by
  have h := (eval_true_iff i s next event enabled).mp evaluated
  rw [h.1]
  simp [Pure32.write]

theorem eval_frame (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) :
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧
      next.addrs = s.addrs ∧ next.preds = s.preds :=
  Pure32.eval_frame evaluated

theorem eval_other (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (evaluated : Eval i s next event) (different : other ≠ i.destination) :
    next.regs other = s.regs other :=
  Pure32.eval_other evaluated (by simpa [lower] using different)

theorem eval_event (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) :
  event = occurrence s i (i.guard.eval s) := by
  simpa [occurrence, lower] using (Pure32.eval_event evaluated)

theorem eval_deterministic (i : Instr) (s next₁ next₂ : Scalar.State) (event₁ event₂ : Occurrence)
    (left : Eval i s next₁ event₁) (right : Eval i s next₂ event₂) :
    next₁ = next₂ ∧ event₁ = event₂ := by
  apply Pure32.eval_deterministic (i := lower i) (s := s) (functional := ?_) left right
  intro words predicates a b ha hb
  simpa [family, Pure32.Family.ofFunction] using (ha.trans hb.symm)

theorem eval_exists (i : Instr) (s : Scalar.State) :
    ∃ next event, Eval i s next event := Pure32.eval_exists (lower i) s

theorem step_origin (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (stepped : Step target program s next event) :
    SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧
      event.pc = s.pc ∧ event.instruction = lower i ∧ Eval i s next event := by
  change Pure32.Step target (program.map lower) s next event at stepped
  obtain ⟨j, fetch, supported, evaluated⟩ := Pure32.step_origin stepped
  have hmap : (program[s.pc]?).map lower = some j := by simpa using fetch
  cases h : program[s.pc]? with
  | none => simp [h] at hmap
  | some original =>
    have hj : lower original = j := Option.some.inj (by simpa [h] using hmap)
    rcases evaluated with ⟨pc, ins, ev⟩
    have ho : j.operation = .selp := by cases j.operation <;> rfl
    change SupportedTarget target at supported
    refine ⟨supported, original, ?_, pc, ?_, ?_⟩
    · simpa [h]
    · simpa [hj] using ins
    · cases hj
      exact ev

theorem step_exists (target : Ptx.Target) (program : List Instr) (s : Scalar.State) (i : Instr)
    (supported : SupportedTarget target) (fetch : program[s.pc]? = some i) :
    ∃ next event, Step target program s next event := by
  have fetch' : (program.map lower)[s.pc]? = some (lower i) := by
    simpa using congrArg (Option.map lower) fetch
  obtain ⟨next, event, h⟩ := Pure32.step_exists (lower i) fetch' (by
    change SupportedTarget target
    exact supported)
  exact ⟨next, event, h⟩

theorem step_no_fetch (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (missing : program[s.pc]? = none) :
    ¬ Step target program s next event := by
  apply Pure32.step_no_fetch (program := program.map lower)
  simpa using congrArg (Option.map lower) missing

theorem step_unsupported_target (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (unsupported : ¬ SupportedTarget target) :
    ¬ Step target program s next event := by
  change ¬ Pure32.Step target (program.map lower) s next event
  intro stepped
  obtain ⟨found, fetch, supported, _⟩ := stepped
  have ho : found.operation = .selp := by cases found.operation <;> rfl
  change SupportedTarget target at supported
  exact unsupported supported

namespace Text

def supportedMnemonic (mnemonic : String) : Bool := mnemonic == "selp.b32"

def encode (i : Instr) : Scalar.Text.Statement :=
  ⟨i.guard, "selp.b32", [.word (.reg i.destination), .word i.left,
    .word i.right, .predicate i.predicate]⟩

def decode (statement : Scalar.Text.Statement) : Except Scalar.Text.DecodeError Instr :=
  if supportedMnemonic statement.mnemonic then
    match statement.operands with
    | [.word (.reg destination), .word left, .word right, .predicate predicate] =>
      .ok ⟨statement.guard, destination, left, right, predicate⟩
    | _ => .error (.invalidOperands statement.mnemonic)
  else .error (.unsupportedMnemonic statement.mnemonic)

theorem decode_encode (i : Instr) : decode (encode i) = .ok i := by
  simp [decode, encode, supportedMnemonic]

theorem decode_iff (statement : Scalar.Text.Statement) (i : Instr) :
    decode statement = .ok i ↔ statement = encode i := by
  constructor
  · intro h
    rcases statement with ⟨guard, mnemonic, operands⟩
    simp only [decode] at h
    by_cases hm : mnemonic = "selp.b32"
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
end Ptx.Scalar.Select32
