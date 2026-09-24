import Ptx.MulHi32
open Ptx
set_option maxRecDepth 4096
set_option linter.unusedVariables false
namespace Ptx.Scalar.MulHi32.Acceptance

example : ∀ (op : Operation) (a b : Word),
    compute op a b = (match op with
      | .unsigned => BitVec.ofNat 32 ((a.toNat * b.toNat) / 2^32)
      | .signed => BitVec.ofInt 32 ((a.toInt * b.toInt) / (2^32 : Int)))
  := @compute_eq

example : ∀ (op : Operation) (words : Fin 2 → Word) (predicates : Fin 0 → Bool) (value : Word),
    family.Results op words predicates value ↔ value = compute op (words 0) (words 1)
  := @results_iff

example : ∀ (i : Instr), (lower i).operation = i.operation
  := @lower_operation

example : ∀ (i : Instr),
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words (⟨0, by decide⟩ : Fin 2) = i.left ∧ (lower i).words (⟨1, by decide⟩ : Fin 2) = i.right
  := @lower_fields

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true),
    Eval i s next event ↔
      next = Pure32.write s i.destination (result i s) ∧ event = occurrence s i true
  := @eval_true_iff

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false),
    Eval i s next event ↔
      next = {s with pc := s.pc + 1} ∧ event = occurrence s i false
  := @eval_false_iff

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) (enabled : i.guard.eval s = true),
    next.regs i.destination = result i s
  := @eval_destination

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event),
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧ next.addrs = s.addrs ∧ next.preds = s.preds
  := @eval_frame

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (evaluated : Eval i s next event) (different : other ≠ i.destination),
    next.regs other = s.regs other
  := @eval_other

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event),
    event = occurrence s i (i.guard.eval s)
  := @eval_event

example : ∀ (i : Instr) (s next₁ next₂ : Scalar.State) (event₁ event₂ : Occurrence)
    (left : Eval i s next₁ event₁) (right : Eval i s next₂ event₂),
    next₁ = next₂ ∧ event₁ = event₂
  := @eval_deterministic

example : ∀ (i : Instr) (s : Scalar.State), ∃ next event, Eval i s next event
  := @eval_exists

example : ∀ (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (stepped : Step target program s next event),
    SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧
      event.pc = s.pc ∧ event.instruction = lower i ∧ Eval i s next event
  := @step_origin

example : ∀ (target : Ptx.Target) (program : List Instr) (s : Scalar.State) (i : Instr)
    (supported : SupportedTarget target) (fetch : program[s.pc]? = some i),
    ∃ next event, Step target program s next event
  := @step_exists

example : ∀ (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (missing : program[s.pc]? = none),
    ¬ Step target program s next event
  := @step_no_fetch

example : ∀ (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (unsupported : ¬ SupportedTarget target),
    ¬ Step target program s next event
  := @step_unsupported_target

example : ∀ (i : Instr), Text.decode (Text.encode i) = .ok i
  := @Text.decode_encode

example : ∀ (statement : Scalar.Text.Statement) (i : Instr),
    Text.decode statement = .ok i ↔ statement = Text.encode i
  := @Text.decode_iff

example : compute .unsigned 0xffffffff 0xffffffff = (0xfffffffe : Word) := by decide
example : compute .signed 0xffffffff 0xffffffff = (0 : Word) := by decide
example : compute .signed 0xffffffff 1 = (0xffffffff : Word) := by decide
example : compute .signed 0x80000000 2 = (0xffffffff : Word) := by decide
example : compute .signed 0x80000000 0x80000000 = (0x40000000 : Word) := by decide
example : compute .unsigned 0x80000000 2 = (1 : Word) := by decide
example : compute .signed 0 0xffffffff = (0 : Word) := by decide
example : SupportedTarget ⟨94,10⟩ := by constructor <;> decide
example : ¬ SupportedTarget ⟨94,9⟩ := by intro h; have : (10 : Nat) ≤ 9 := h.2; omega
example : ¬ SupportedTarget ⟨93,90⟩ := by intro h; have := h.1; contradiction
example : Text.decode ⟨.pred 3 false, "mul.hi.u32", [.word (.reg 0), .word (.reg 0), .word (.reg 0)]⟩ = .ok (⟨.pred 3 false, .unsigned, 0, .reg 0, .reg 0⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "mul.hi.u32", []⟩ = .error (.invalidOperands "mul.hi.u32") := by rfl
example : Text.decode ⟨.pred 3 false, "mul.hi.s32", [.word (.reg 0), .word (.reg 0), .word (.reg 0)]⟩ = .ok (⟨.pred 3 false, .signed, 0, .reg 0, .reg 0⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "mul.hi.s32", []⟩ = .error (.invalidOperands "mul.hi.s32") := by rfl
example : Text.decode ⟨.always, "mul.lo.u32", []⟩ = .error (.unsupportedMnemonic "mul.lo.u32") := by rfl
example : Text.decode ⟨.always, "mul.wide.s32", []⟩ = .error (.unsupportedMnemonic "mul.wide.s32") := by rfl
example : Text.decode ⟨.always, "mul.hi.u64", []⟩ = .error (.unsupportedMnemonic "mul.hi.u64") := by rfl
example : Text.decode ⟨.always, "unknown", []⟩ = .error (.unsupportedMnemonic "unknown") := by rfl
private def incoming : Scalar.State := ⟨7, fun _ => 1, fun _ => 0, fun _ => true, [11,22]⟩
private def tested : Instr := ⟨.pred 3 true, .unsigned, 0, .reg 0, .reg 0⟩
example : Eval tested incoming (Pure32.write incoming 0 (result tested incoming)) (occurrence incoming tested true) := (eval_true_iff tested incoming _ _ (by rfl)).mpr ⟨rfl,rfl⟩
example : (occurrence incoming tested true).reads = [.predicate 3, .word 0, .word 0] := by rfl
private def skipped : Instr := {tested with guard := .pred 3 false}
example : Eval skipped incoming {incoming with pc := 8} (occurrence incoming skipped false) := (eval_false_iff skipped incoming _ _ (by rfl)).mpr ⟨rfl,rfl⟩
example : (occurrence incoming skipped false).reads = [.predicate 3] := by rfl
end Ptx.Scalar.MulHi32.Acceptance
