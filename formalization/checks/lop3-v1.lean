import Ptx.Lop3
open Ptx
set_option linter.unusedVariables false
set_option maxRecDepth 4096
namespace Ptx.Scalar.Lop3.Acceptance

example : ∀ (op : Operation) (a b c : Word) (bit : Nat) (bound : bit < 32),
    (compute op a b c).getLsbD bit = (op.getLsbD ((if a.getLsbD bit then 4 else 0) + (if b.getLsbD bit then 2 else 0) + (if c.getLsbD bit then 1 else 0)))
  := @compute_bit

example : ∀ (op : Operation) (words : Fin 3 → Word) (predicates : Fin 0 → Bool) (value : Word),
    family.Results op words predicates value ↔ value = compute op (words 0) (words 1) (words 2)
  := @results_iff

example : ∀ (i : Instr), (lower i).operation = i.operation
  := @lower_operation

example : ∀ (i : Instr),
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words (⟨0, by decide⟩ : Fin 3) = i.first ∧ (lower i).words (⟨1, by decide⟩ : Fin 3) = i.second ∧ (lower i).words (⟨2, by decide⟩ : Fin 3) = i.third
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

example : compute 0xf0 0x12345678 0 0 = (0x12345678 : Word) := by decide
example : compute 0xcc 0 0xabcdef01 0 = (0xabcdef01 : Word) := by decide
example : compute 0xaa 0 0 0xffffffff = (0xffffffff : Word) := by decide
example : compute 0x80 0xf0f0 0xff00 0xffff = (0xf000 : Word) := by decide
example : compute 0x96 0x1234 0x5555 0xffff = (0xb89e : Word) := by decide
example : compute 0 0xffffffff 0xffffffff 0xffffffff = (0 : Word) := by decide
example : compute 255 0 0 0 = (0xffffffff : Word) := by decide
example : SupportedTarget ⟨94,50⟩ := by constructor <;> decide
example : ¬ SupportedTarget ⟨94,49⟩ := by intro h; have : (50 : Nat) ≤ 49 := h.2; omega
example : ¬ SupportedTarget ⟨93,90⟩ := by intro h; have := h.1; contradiction
example : Text.decode ⟨.pred 3 false, "lop3.b32", [.word (.reg 0), .word (.reg 0), .word (.reg 0), .word (.reg 0), .word (.imm 0x96)]⟩ = .ok (⟨.pred 3 false, 0x96, 0, .reg 0, .reg 0, .reg 0⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "lop3.b32", []⟩ = .error (.invalidOperands "lop3.b32") := by rfl
example : Text.decode ⟨.always, "lop3.and.b32", []⟩ = .error (.unsupportedMnemonic "lop3.and.b32") := by rfl
example : Text.decode ⟨.always, "lop3.or.b32", []⟩ = .error (.unsupportedMnemonic "lop3.or.b32") := by rfl
example : Text.decode ⟨.always, "lop3.b64", []⟩ = .error (.unsupportedMnemonic "lop3.b64") := by rfl
example : Text.decode ⟨.always, "unknown", []⟩ = .error (.unsupportedMnemonic "unknown") := by rfl
private def incoming : Scalar.State := ⟨7, fun _ => 1, fun _ => 0, fun _ => true, [11,22]⟩
private def tested : Instr := ⟨.pred 3 true, 0x96, 0, .reg 0, .reg 0, .reg 0⟩
example : Eval tested incoming (Pure32.write incoming 0 (result tested incoming)) (occurrence incoming tested true) := (eval_true_iff tested incoming _ _ (by rfl)).mpr ⟨rfl,rfl⟩
example : (occurrence incoming tested true).reads = [.predicate 3, .word 0, .word 0, .word 0] := by rfl
private def skipped : Instr := {tested with guard := .pred 3 false}
example : Eval skipped incoming {incoming with pc := 8} (occurrence incoming skipped false) := (eval_false_iff skipped incoming _ _ (by rfl)).mpr ⟨rfl,rfl⟩
example : (occurrence incoming skipped false).reads = [.predicate 3] := by rfl
example : Text.decode ⟨.always, "lop3.b32", [.word (.reg 0), .word (.reg 0), .word (.reg 1), .word (.reg 2), .word (.reg 3)]⟩ = .error (.invalidOperands "lop3.b32") := by rfl
example : Text.decode ⟨.always, "lop3.b32", [.word (.reg 0), .word (.reg 0), .word (.reg 1), .word (.reg 2), .word (.imm 256)]⟩ = .error (.invalidOperands "lop3.b32") := by rfl
end Ptx.Scalar.Lop3.Acceptance
