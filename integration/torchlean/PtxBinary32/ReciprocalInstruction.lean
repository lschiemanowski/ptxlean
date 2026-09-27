import PtxBinary32.Reciprocal
import Ptx.ScalarText
import Ptx.Environment

/-! Explicit nearest-even binary32 reciprocal scalar leaf. -/
namespace Ptx.Scalar.Reciprocal

structure Instr where
  guard : Scalar.Guard := .always
  destination : Nat
  source : Scalar.Operand32
  deriving DecidableEq, Repr

structure Occurrence where
  pc : Nat
  instruction : Instr
  executed : Bool
  reads : List Scalar.Register
  writes : List Scalar.Register
  memory : Option Scalar.MemoryEffect
  deriving DecidableEq, Repr

def occurrence (s : Scalar.State) (i : Instr) (executed : Bool) : Occurrence :=
  ⟨s.pc, i, executed, i.guard.reads ++ (if executed then i.source.reads else []),
    (if executed then [.word i.destination] else []), none⟩

def SupportedTarget (target : Ptx.Target) : Prop :=
  target.isa = 94 ∧ 20 ≤ target.sm

inductive Eval (i : Instr) : Scalar.State → Scalar.State → Occurrence → Prop
  | skipped {s} (disabled : i.guard.eval s = false) :
      Eval i s {s with pc := s.pc + 1} (occurrence s i false)
  | executed {s value} (enabled : i.guard.eval s = true)
      (result : Ptx.Binary32.Reciprocal.Results (i.source.eval s) value) :
      Eval i s {{s with pc := s.pc + 1} with
        regs := Scalar.update s.regs i.destination value} (occurrence s i true)

def Step (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) : Prop :=
  SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧ Eval i s next event

theorem eval_true_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true) :
    Eval i s next event ↔ ∃ value,
      Ptx.Binary32.Reciprocal.Results (i.source.eval s) value ∧
      next = {s with pc := s.pc+1, regs := Scalar.update s.regs i.destination value} ∧
      event = occurrence s i true := by
  constructor
  · intro h; cases h with
    | skipped disabled => simp [enabled] at disabled
    | executed _ result => exact ⟨_, result, rfl, rfl⟩
  · rintro ⟨value, result, rfl, rfl⟩; exact .executed enabled result

theorem eval_false_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false) :
    Eval i s next event ↔ next = {s with pc := s.pc+1} ∧ event = occurrence s i false := by
  constructor
  · intro h; cases h with
    | skipped _ => exact ⟨rfl, rfl⟩
    | executed enabled _ => simp [disabled] at enabled
  · rintro ⟨rfl, rfl⟩; exact .skipped disabled

theorem eval_destination (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) (enabled : i.guard.eval s = true) :
    Ptx.Binary32.Reciprocal.Results (i.source.eval s) (next.regs i.destination) := by
  cases hEval with
  | skipped disabled => simp [enabled] at disabled
  | executed _ result => simpa using result

theorem eval_frame (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) :
    next.pc = s.pc+1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds := by
  cases hEval <;> simp_all

theorem eval_other (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (hEval : Eval i s next event) (different : other ≠ i.destination) :
    next.regs other = s.regs other := by
  cases hEval with
  | skipped _ => rfl
  | executed _ _ => simp [Scalar.update, different]

theorem eval_event (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) : event = occurrence s i (i.guard.eval s) := by
  cases hEval with
  | skipped h => simp [h]
  | executed h _ => simp [h]

theorem eval_exists (i : Instr) (s : Scalar.State) : ∃ next event, Eval i s next event := by
  by_cases h : i.guard.eval s = true
  · obtain ⟨value, hv⟩ := Ptx.Binary32.Reciprocal.results_exists (i.source.eval s)
    exact ⟨{s with pc := s.pc+1, regs := Scalar.update s.regs i.destination value},
      occurrence s i true, .executed h hv⟩
  · have hf : i.guard.eval s = false := Bool.eq_false_of_not_eq_true h
    exact ⟨{s with pc := s.pc+1}, occurrence s i false, .skipped hf⟩

theorem step_origin (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (hStep : Step target program s next event) :
    SupportedTarget target ∧ ∃ i,
      program[s.pc]? = some i ∧ event.instruction = i ∧ Eval i s next event := by
  rcases hStep with ⟨hs, i, fetch, he⟩
  exact ⟨hs, i, fetch, by cases he <;> rfl, he⟩

theorem step_exists (target : Ptx.Target) (program : List Instr) (s : Scalar.State)
    (i : Instr) (supported : SupportedTarget target) (fetch : program[s.pc]? = some i) :
    ∃ next event, Step target program s next event := by
  obtain ⟨next, event, he⟩ := eval_exists i s
  exact ⟨next, event, supported, i, fetch, he⟩

theorem step_no_fetch (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (missing : program[s.pc]? = none) :
    ¬ Step target program s next event := by
  rintro ⟨_, i, fetch, _⟩; rw [missing] at fetch; contradiction

theorem step_unsupported_target (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (unsupported : ¬ SupportedTarget target) :
    ¬ Step target program s next event := by
  rintro ⟨hs, _⟩; exact unsupported hs

namespace Text

def mnemonic : String := "rcp.rn.f32"
def supportedMnemonic (name : String) : Bool := name == "rcp.rn.f32"

def encode (i : Instr) : Scalar.Text.Statement :=
  ⟨i.guard, mnemonic, [.word (.reg i.destination), .word i.source]⟩

def decode (statement : Scalar.Text.Statement) : Except Scalar.Text.DecodeError Instr :=
  if statement.mnemonic == mnemonic then
    match statement.operands with
    | [.word (.reg d), .word source] => .ok ⟨statement.guard, d, source⟩
    | _ => .error (.invalidOperands statement.mnemonic)
  else .error (.unsupportedMnemonic statement.mnemonic)

theorem decode_encode (i : Instr) : decode (encode i) = .ok i := by
  cases i with | mk g d s => rfl

theorem decode_iff (statement : Scalar.Text.Statement) (i : Instr) :
    decode statement = .ok i ↔ statement = encode i := by
  constructor
  · intro h
    cases statement with
    | mk g m ops =>
      cases i with
      | mk gi di si =>
        by_cases hm : m = mnemonic
        · subst m
          simp only [decode] at h
          cases ops with
          | nil => simp [decode] at h
          | cons first rest => cases first with
            | word first => cases first with
              | reg d => cases rest with
                | nil => simp [decode] at h
                | cons second rest2 => cases second with
                  | word source => cases rest2 with
                    | nil =>
                        simp only [decode] at h
                        rcases h with ⟨rfl, rfl, rfl⟩
                        rfl
                    | cons _ _ => simp [decode] at h
                  | _ => simp [decode] at h
              | imm _ => simp [decode] at h
            | _ => simp [decode] at h
        · simp [decode, hm] at h
  · rintro rfl; exact decode_encode i

end Text
end Ptx.Scalar.Reciprocal
