import Ptx.Lop3
open Ptx
set_option linter.unusedVariables false
set_option maxRecDepth 4096
namespace Ptx.Scalar.Lop3.Acceptance

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
