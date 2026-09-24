import Ptx.Bfi32
open Ptx
set_option linter.unusedVariables false
set_option maxRecDepth 4096
namespace Ptx.Scalar.Bfi32.Acceptance

example : ∀ (op : Operation) (a b c d : Word) (bit : Nat) (bound : bit < 32),
    (compute op a b c d).getLsbD bit = (if c.toNat % 256 ≤ bit ∧ bit < c.toNat % 256 + d.toNat % 256 then a.getLsbD (bit - c.toNat % 256) else b.getLsbD bit)
  := @compute_bit

example : ∀ (op : Operation) (words : Fin 4 → Word) (predicates : Fin 0 → Bool) (value : Word),
    family.Results op words predicates value ↔ value = compute op (words 0) (words 1) (words 2) (words 3)
  := @results_iff

example : ∀ (i : Instr), (lower i).operation = i.operation
  := @lower_operation

example : ∀ (i : Instr),
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words (⟨0, by decide⟩ : Fin 4) = i.insert ∧ (lower i).words (⟨1, by decide⟩ : Fin 4) = i.base ∧ (lower i).words (⟨2, by decide⟩ : Fin 4) = i.position ∧ (lower i).words (⟨3, by decide⟩ : Fin 4) = i.length
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

example : compute .insert 0xf 0x12345678 4 4 = (0x123456f8 : Word) := by decide
example : compute .insert 0 0xffffffff 4 8 = (0xfffff00f : Word) := by decide
example : compute .insert 0xffffffff 0 31 255 = (0x80000000 : Word) := by decide
example : compute .insert 1 123 32 1 = (123 : Word) := by decide
example : compute .insert 0 123 0 0 = (123 : Word) := by decide
example : compute .insert 0xf 0x12345678 260 260 = (0x123456f8 : Word) := by decide
example : compute .insert 0xffffffff 42 0 256 = (42 : Word) := by decide
example : compute .insert 0xffffffff 42 0xffffffff 0xffffffff = (42 : Word) := by decide
example : SupportedTarget ⟨94,20⟩ := by constructor <;> decide
example : ¬ SupportedTarget ⟨94,19⟩ := by intro h; have : (20 : Nat) ≤ 19 := h.2; omega
example : ¬ SupportedTarget ⟨93,90⟩ := by intro h; have := h.1; contradiction
example : Text.decode ⟨.pred 3 false, "bfi.b32", [.word (.reg 0), .word (.reg 0), .word (.reg 0), .word (.reg 0), .word (.reg 0)]⟩ = .ok (⟨.pred 3 false, .insert, 0, .reg 0, .reg 0, .reg 0, .reg 0⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "bfi.b32", []⟩ = .error (.invalidOperands "bfi.b32") := by rfl
example : Text.decode ⟨.always, "bfi.b64", []⟩ = .error (.unsupportedMnemonic "bfi.b64") := by rfl
example : Text.decode ⟨.always, "bfi.u32", []⟩ = .error (.unsupportedMnemonic "bfi.u32") := by rfl
example : Text.decode ⟨.always, "unknown", []⟩ = .error (.unsupportedMnemonic "unknown") := by rfl
private def incoming : Scalar.State := ⟨7, fun _ => 1, fun _ => 0, fun _ => true, [11,22]⟩
private def tested : Instr := ⟨.pred 3 true, .insert, 0, .reg 0, .reg 0, .reg 0, .reg 0⟩
example : Eval tested incoming (Pure32.write incoming 0 (result tested incoming)) (occurrence incoming tested true) := (eval_true_iff tested incoming _ _ (by rfl)).mpr ⟨rfl,rfl⟩
example : (occurrence incoming tested true).reads = [.predicate 3, .word 0, .word 0, .word 0, .word 0] := by rfl
private def skipped : Instr := {tested with guard := .pred 3 false}
example : Eval skipped incoming {incoming with pc := 8} (occurrence incoming skipped false) := (eval_false_iff skipped incoming _ _ (by rfl)).mpr ⟨rfl,rfl⟩
example : (occurrence incoming skipped false).reads = [.predicate 3] := by rfl
end Ptx.Scalar.Bfi32.Acceptance
