import Ptx.Bfi32
open Ptx
set_option linter.unusedVariables false
set_option maxRecDepth 4096
namespace Ptx.Scalar.Bfi32.Acceptance

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
