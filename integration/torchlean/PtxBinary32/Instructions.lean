import PtxBinary32
import Ptx.ScalarText
import Ptx.Environment

/-! Explicit `add.rn.f32` and `mul.rn.f32` scalar leaves. Immediate words in
this context are already-decoded exact `0f`/`0F` binary32 bit literals; no
integer-to-float conversion or decimal parsing is performed. Register type
compatibility (`.b32`/`.f32`) remains a frontend obligation. This models the
conservative `Ptx.Binary32.Results` envelope, not a particular GPU result. -/
namespace Ptx.Scalar.Binary32

structure Instr where
  guard : Scalar.Guard := .always
  operation : Ptx.Binary32.Operation
  destination : Nat
  left : Scalar.Operand32
  right : Scalar.Operand32
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
  ⟨s.pc, i, executed, i.guard.reads ++
    (if executed then i.left.reads ++ i.right.reads else []),
    (if executed then [.word i.destination] else []), none⟩

def SupportedTarget (target : Ptx.Target) : Prop :=
  target.isa = 94 ∧ 20 ≤ target.sm

inductive Eval (i : Instr) : Scalar.State → Scalar.State → Occurrence → Prop
  | skipped {s} (disabled : i.guard.eval s = false) :
      Eval i s {s with pc := s.pc + 1} (occurrence s i false)
  | executed {s value} (enabled : i.guard.eval s = true)
      (result : Ptx.Binary32.Results i.operation (i.left.eval s) (i.right.eval s) value) :
      Eval i s {{s with pc := s.pc + 1} with
        regs := Scalar.update s.regs i.destination value} (occurrence s i true)

def Step (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) : Prop :=
  SupportedTarget target ∧
    ∃ instruction, program[s.pc]? = some instruction ∧ Eval instruction s next event

theorem eval_true_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true) :
    Eval i s next event ↔ ∃ value,
      Ptx.Binary32.Results i.operation (i.left.eval s) (i.right.eval s) value ∧
      next = {{s with pc := s.pc + 1} with regs := Scalar.update s.regs i.destination value} ∧
      event = occurrence s i true := by
  constructor
  · intro h; cases h with
    | skipped disabled => simp [enabled] at disabled
    | executed _ result => exact ⟨_, result, rfl, rfl⟩
  · rintro ⟨value, result, rfl, rfl⟩; exact .executed enabled result

theorem eval_false_iff (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false) :
    Eval i s next event ↔ next = {s with pc := s.pc + 1} ∧ event = occurrence s i false := by
  constructor
  · intro h; cases h with
    | skipped _ => exact ⟨rfl, rfl⟩
    | executed enabled _ => simp [disabled] at enabled
  · rintro ⟨rfl, rfl⟩; exact .skipped disabled

theorem eval_destination (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) (enabled : i.guard.eval s = true) :
    Ptx.Binary32.Results i.operation (i.left.eval s) (i.right.eval s)
      (next.regs i.destination) := by
  cases hEval with
  | skipped disabled => simp [enabled] at disabled
  | executed _ result => simpa using result

theorem eval_frame (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (hEval : Eval i s next event) :
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds := by
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
  · obtain ⟨value, hv⟩ := Ptx.Binary32.results_exists i.operation (i.left.eval s) (i.right.eval s)
    exact ⟨{{s with pc := s.pc + 1} with regs := Scalar.update s.regs i.destination value},
      occurrence s i true, .executed h hv⟩
  · have hf : i.guard.eval s = false := Bool.eq_false_of_not_eq_true h
    exact ⟨{s with pc := s.pc + 1}, occurrence s i false, .skipped hf⟩

theorem step_origin (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence)
    (hStep : Step target program s next event) :
    SupportedTarget target ∧ ∃ i,
      program[s.pc]? = some i ∧ event.instruction = i ∧ Eval i s next event := by
  rcases hStep with ⟨hs, i, fetch, he⟩
  exact ⟨hs, i, fetch, by cases he <;> rfl, he⟩

theorem step_exists (target : Ptx.Target) (program : List Instr)
    (s : Scalar.State) (i : Instr) (supported : SupportedTarget target)
    (fetch : program[s.pc]? = some i) : ∃ next event, Step target program s next event := by
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

def mnemonic : Ptx.Binary32.Operation → String
  | .add => "add.rn.f32"
  | .mul => "mul.rn.f32"

def supportedMnemonic (name : String) : Bool := name == "add.rn.f32" || name == "mul.rn.f32"

def decode (statement : Scalar.Text.Statement) : Except Scalar.Text.DecodeError Instr :=
  let operation := if statement.mnemonic == "add.rn.f32" then some .add
    else if statement.mnemonic == "mul.rn.f32" then some .mul else none
  match operation with
  | none => .error (.unsupportedMnemonic statement.mnemonic)
  | some op => match statement.operands with
    | [.word (.reg d), .word a, .word b] => .ok ⟨statement.guard, op, d, a, b⟩
    | _ => .error (.invalidOperands statement.mnemonic)

def encode (instruction : Instr) : Scalar.Text.Statement :=
  ⟨instruction.guard, mnemonic instruction.operation,
    [.word (.reg instruction.destination), .word instruction.left, .word instruction.right]⟩

theorem decode_encode (i : Instr) : decode (encode i) = .ok i := by
  cases i with
  | mk g op d a b => cases op <;> rfl

theorem decode_iff (statement : Scalar.Text.Statement) (i : Instr) :
    decode statement = .ok i ↔ statement = encode i := by
  constructor
  · intro h
    cases statement with
    | mk g m ops =>
      cases i with
      | mk gi oi di li ri =>
        by_cases hm : m = "add.rn.f32"
        · subst m
          cases oi with
          | add =>
            simp [decode] at h
            split at h
            · injection h with hInstr
              cases hInstr
              rfl
            · contradiction
          | mul => simp [decode] at h; split at h <;> simp_all
        · by_cases hm' : m = "mul.rn.f32"
          · subst m
            cases oi with
            | add => simp [decode] at h; split at h <;> simp_all
            | mul =>
              simp [decode] at h
              split at h
              · injection h with hInstr
                cases hInstr
                rfl
              · contradiction
          · simp [decode, hm, hm'] at h
  · rintro rfl; exact (decode_encode i)

end Text

/-! Small kernel-checked source examples. The numerical witnesses deliberately
use the reviewed reference envelope; they do not assert hardware NaN payloads. -/
private def demoState : Scalar.State :=
  ⟨4, fun _ => 0, fun _ => 0, fun _ => false, [17, 23]⟩

private def bits15 : Word := 0x3fc00000
private def bits225 : Word := 0x40100000
private def bits375 : Word := 0x40700000
private def bits3375 : Word := 0x40580000

example : Text.mnemonic .add = "add.rn.f32" := rfl
example : Text.mnemonic .mul = "mul.rn.f32" := rfl

example : Ptx.Binary32.Results .add bits15 bits225 bits375 := by
  change Ptx.Binary32.Envelope (Ptx.Binary32.reference .add bits15 bits225) bits375
  exact Ptx.Binary32.envelope_self _

example : Ptx.Binary32.Results .mul bits15 bits225 bits3375 := by
  change Ptx.Binary32.Envelope (Ptx.Binary32.reference .mul bits15 bits225) bits3375
  exact Ptx.Binary32.envelope_self _

example : Ptx.Binary32.Results .add 0x80000000 0x00000000
    (Ptx.Binary32.reference .add 0x80000000 0x00000000) := by
  change Ptx.Binary32.Envelope _ _
  exact Ptx.Binary32.envelope_self _

example : Ptx.Binary32.Results .mul 0x00000001 0x3f800000
    (Ptx.Binary32.reference .mul 0x00000001 0x3f800000) := by
  change Ptx.Binary32.Envelope _ _
  exact Ptx.Binary32.envelope_self _

example (nanRef : Word) (nanOut : Word) (h : Ptx.Binary32.isNaN nanRef = true)
    (outNaN : Ptx.Binary32.isNaN nanOut = true) :
    Ptx.Binary32.Envelope nanRef nanOut :=
  (Ptx.Binary32.envelope_nan nanRef nanOut h).2 outNaN

example (finiteRef mismatch : Word) (finite : Ptx.Binary32.isFinite finiteRef = true)
    (different : mismatch ≠ finiteRef) :
    ¬ Ptx.Binary32.Envelope finiteRef mismatch := by
  intro allowed
  exact different (Ptx.Binary32.envelope_finite_eq finiteRef mismatch finite allowed)

example : ∃ next event,
    Eval ⟨.always, .add, 3, .reg 3, .imm bits225⟩ demoState next event := by
  exact eval_exists _ _

example : ∃ next event,
    Eval ⟨.always, .mul, 3, .imm bits15, .reg 3⟩ demoState next event := by
  exact eval_exists _ _

example : ∃ next event,
    Eval ⟨.always, .add, 3, .reg 7, .reg 7⟩ demoState next event := by
  exact eval_exists _ _

example : ∃ next event,
    Eval ⟨.always, .mul, 3, .reg 3, .reg 3⟩ demoState next event := by
  exact eval_exists _ _

example : Eval ⟨.pred 2 true, .add, 0, .imm 0x7f800001, .imm 0x7fc00002⟩
    {demoState with preds := fun _ => false} 
    {{demoState with preds := fun _ => false} with pc := 5}
    (occurrence {demoState with preds := fun _ => false}
      ⟨.pred 2 true, .add, 0, .imm 0x7f800001, .imm 0x7fc00002⟩ false) := by
  apply Eval.skipped
  rfl

example : ∃ next event,
    Eval ⟨.pred 2 true, .mul, 0, .imm bits15, .imm bits225⟩
      {demoState with preds := fun n => n == 2} next event := by
  apply Exists.elim (Ptx.Binary32.results_exists .mul bits15 bits225)
  intro value result
  refine ⟨{{{demoState with preds := fun n => n == 2} with pc := 5} with
    regs := Scalar.update ({demoState with preds := fun n => n == 2}).regs 0 value},
    occurrence {demoState with preds := fun n => n == 2}
      ⟨.pred 2 true, .mul, 0, .imm bits15, .imm bits225⟩ true, ?_⟩
  apply Eval.executed
  · simp [Scalar.Guard.eval]
  · exact result

example : Text.decode ⟨.always, "add.f32", []⟩ =
    .error (.unsupportedMnemonic "add.f32") := rfl

example : Text.decode ⟨.always, "add.rn.f32", [.word (.imm 0), .word (.imm 1), .word (.imm 2)]⟩ =
    .error (.invalidOperands "add.rn.f32") := rfl

example : Text.decode ⟨.always, "mul.rn.f32", [.word (.reg 0), .word (.imm 1)]⟩ =
    .error (.invalidOperands "mul.rn.f32") := rfl

example : Text.decode ⟨.always, "mul.f32", []⟩ =
    .error (.unsupportedMnemonic "mul.f32") := rfl
example : Text.decode ⟨.always, "add.rz.f32", []⟩ =
    .error (.unsupportedMnemonic "add.rz.f32") := rfl
example : Text.decode ⟨.always, "mul.rm.f32", []⟩ =
    .error (.unsupportedMnemonic "mul.rm.f32") := rfl
example : Text.decode ⟨.always, "add.rp.f32", []⟩ =
    .error (.unsupportedMnemonic "add.rp.f32") := rfl
example : Text.decode ⟨.always, "mul.ftz.f32", []⟩ =
    .error (.unsupportedMnemonic "mul.ftz.f32") := rfl
example : Text.decode ⟨.always, "add.sat.f32", []⟩ =
    .error (.unsupportedMnemonic "add.sat.f32") := rfl
example : Text.decode ⟨.always, "mul.rn.f64", []⟩ =
    .error (.unsupportedMnemonic "mul.rn.f64") := rfl
example : Text.decode ⟨.always, "add.rn.f32x2", []⟩ =
    .error (.unsupportedMnemonic "add.rn.f32x2") := rfl
example : Text.decode ⟨.always, "add.u32", []⟩ =
    .error (.unsupportedMnemonic "add.u32") := rfl
example : Text.decode ⟨.always, "mul.lo.u32", []⟩ =
    .error (.unsupportedMnemonic "mul.lo.u32") := rfl
example : Text.decode ⟨.always, "mul.rn.f32", [.word (.reg 0), .word (.reg 1), .address (.imm 0)]⟩ =
    .error (.invalidOperands "mul.rn.f32") := rfl

theorem signed_zero_bits :
    Ptx.Binary32.Results .mul 0x80000000 0x3f800000 0x80000000 := by
  change Ptx.Binary32.Envelope
    (Ptx.Binary32.reference .mul 0x80000000 0x3f800000) 0x80000000
  exact Ptx.Binary32.envelope_self _

theorem subnormal_bits : Ptx.Binary32.Results .add 1 1 2 := by
  change Ptx.Binary32.Envelope (Ptx.Binary32.reference .add 1 1) 2
  exact Ptx.Binary32.envelope_self _

theorem negative_guard_exec (s : Scalar.State) (predFalse : s.preds 7 = false) :
    Eval ⟨.pred 7 false, .mul, 2, .imm 0x3fc00000, .imm 0x40100000⟩ s
      {{s with pc := s.pc + 1} with regs := Scalar.update s.regs 2 0x40580000}
      (occurrence s ⟨.pred 7 false, .mul, 2, .imm 0x3fc00000, .imm 0x40100000⟩ true) := by
  apply Eval.executed
  · simp [Scalar.Guard.eval, predFalse]
  · change Ptx.Binary32.Envelope
      (Ptx.Binary32.reference .mul 0x3fc00000 0x40100000) 0x40580000
    exact Ptx.Binary32.envelope_self _

theorem negative_guard_skip (s : Scalar.State) (predTrue : s.preds 7 = true) :
    Eval ⟨.pred 7 false, .mul, 2, .imm 0x3fc00000, .imm 0x40100000⟩ s
      {s with pc := s.pc + 1}
      (occurrence s ⟨.pred 7 false, .mul, 2, .imm 0x3fc00000, .imm 0x40100000⟩ false) := by
  apply Eval.skipped
  simp [Scalar.Guard.eval, predTrue]

theorem alias_add_bits (s : Scalar.State) (sourceBits : s.regs 3 = 0x3fc00000) :
    Eval ⟨.always, .add, 3, .reg 3, .reg 3⟩ s
      {{s with pc := s.pc + 1} with regs := Scalar.update s.regs 3 0x40400000}
      (occurrence s ⟨.always, .add, 3, .reg 3, .reg 3⟩ true) := by
  apply Eval.executed
  · rfl
  · change Ptx.Binary32.Results .add (s.regs 3) (s.regs 3) 0x40400000
    rw [sourceBits]
    change Ptx.Binary32.Envelope
      (Ptx.Binary32.reference .add 0x3fc00000 0x3fc00000) 0x40400000
    exact Ptx.Binary32.envelope_self _

end Ptx.Scalar.Binary32
