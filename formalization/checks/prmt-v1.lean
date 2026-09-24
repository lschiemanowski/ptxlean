import Ptx.Prmt32
open Ptx
set_option linter.unusedVariables false
set_option maxRecDepth 4096
namespace Ptx.Scalar.Prmt32.Acceptance

example : ∀ (op : Operation) (a b c : Word) (bit : Nat) (bound : bit < 32),
    (compute op a b c).getLsbD bit = (let selector := (c.toNat / 2 ^ (4 * (bit / 8))) % 16
     let source := if selector % 8 < 4 then a else b
     source.getLsbD (8 * (selector % 4) + (if 8 ≤ selector then 7 else bit % 8)))
  := @compute_bit

example : ∀ (op : Operation) (words : Fin 3 → Word) (predicates : Fin 0 → Bool) (value : Word),
    family.Results op words predicates value ↔ value = compute op (words 0) (words 1) (words 2)
  := @results_iff

example : ∀ (i : Instr), (lower i).operation = i.operation
  := @lower_operation

example : ∀ (i : Instr),
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words (⟨0, by decide⟩ : Fin 3) = i.first ∧ (lower i).words (⟨1, by decide⟩ : Fin 3) = i.second ∧ (lower i).words (⟨2, by decide⟩ : Fin 3) = i.control
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

example : compute .permute 0x44332211 0x88776655 0x3210 = (0x44332211 : Word) := by decide
example : compute .permute 0x44332211 0x88776655 0x7654 = (0x88776655 : Word) := by decide
example : compute .permute 0x44332211 0x88776655 0x123 = (0x11223344 : Word) := by decide
example : compute .permute 0x44332211 0x88776655 0x4567 = (0x55667788 : Word) := by decide
example : compute .permute 0x44332211 0x88776655 0x5410 = (0x66552211 : Word) := by decide
example : compute .permute 0x44332211 0x88776655 0x7777 = (0x88888888 : Word) := by decide
example : compute .permute 0x44332211 0x88776655 0x8000 = (0x111111 : Word) := by decide
example : compute .permute 0x44332211 0x88776655 0xfedc = (0xff000000 : Word) := by decide
example : compute .permute 0x44332211 0x88776655 0xba98 = (0x0 : Word) := by decide
example : compute .permute 0x44332211 0x88776655 0xffff = (0xffffffff : Word) := by decide
example : compute .permute 0x44332211 0x88776655 0xabcd5410 = (0x66552211 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3210 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0xba98 = (0xffff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0xfedc = (0xffff0000 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0xf80b = (0xff000000 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x12340000 = (0x0 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0xffffffff = (0xffffffff : Word) := by decide

example : SupportedTarget ⟨94,20⟩ := by constructor <;> decide
example : ¬ SupportedTarget ⟨94,19⟩ := by intro h; have : (20 : Nat) ≤ 19 := h.2; omega
example : ¬ SupportedTarget ⟨93,90⟩ := by intro h; have := h.1; contradiction
example : Text.decode ⟨.pred 3 false, "prmt.b32", [.word (.reg 0), .word (.reg 0), .word (.reg 0), .word (.reg 0)]⟩ = .ok (⟨.pred 3 false, .permute, 0, .reg 0, .reg 0, .reg 0⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "prmt.b32", []⟩ = .error (.invalidOperands "prmt.b32") := by rfl
example : Text.decode ⟨.always, "prmt.b32", [.word (.imm 0), .word (.reg 1), .word (.reg 2), .word (.reg 3)]⟩ = .error (.invalidOperands "prmt.b32") := by rfl
example : Text.decode ⟨.always, "prmt.b32", [.word (.reg 0), .word (.reg 1), .word (.reg 2), .word (.imm 0xffffffff)]⟩ = .ok (⟨.always, .permute, 0, .reg 1, .reg 2, .imm 0xffffffff⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "prmt.b32.f4e", []⟩ = .error (.unsupportedMnemonic "prmt.b32.f4e") := by rfl
example : Text.decode ⟨.always, "prmt.b32.b4e", []⟩ = .error (.unsupportedMnemonic "prmt.b32.b4e") := by rfl
example : Text.decode ⟨.always, "prmt.b32.rc8", []⟩ = .error (.unsupportedMnemonic "prmt.b32.rc8") := by rfl
example : Text.decode ⟨.always, "prmt.b32.ecl", []⟩ = .error (.unsupportedMnemonic "prmt.b32.ecl") := by rfl
example : Text.decode ⟨.always, "prmt.b32.ecr", []⟩ = .error (.unsupportedMnemonic "prmt.b32.ecr") := by rfl
example : Text.decode ⟨.always, "prmt.b32.rc16", []⟩ = .error (.unsupportedMnemonic "prmt.b32.rc16") := by rfl
example : Text.decode ⟨.always, "prmt.b64", []⟩ = .error (.unsupportedMnemonic "prmt.b64") := by rfl
example : Text.decode ⟨.always, "unknown", []⟩ = .error (.unsupportedMnemonic "unknown") := by rfl
private def incoming : Scalar.State := ⟨7, fun _ => 1, fun _ => 0, fun _ => true, [11,22]⟩
private def tested : Instr := ⟨.pred 3 true, .permute, 0, .reg 0, .reg 0, .reg 0⟩
example : Eval tested incoming (Pure32.write incoming 0 (result tested incoming)) (occurrence incoming tested true) := (eval_true_iff tested incoming _ _ (by rfl)).mpr ⟨rfl,rfl⟩
example : (occurrence incoming tested true).reads = [.predicate 3, .word 0, .word 0, .word 0] := by rfl
private def skipped : Instr := {tested with guard := .pred 3 false}
example : Eval skipped incoming {incoming with pc := 8} (occurrence incoming skipped false) := (eval_false_iff skipped incoming _ _ (by rfl)).mpr ⟨rfl,rfl⟩
example : (occurrence incoming skipped false).reads = [.predicate 3] := by rfl
example : compute .permute 0x7f80ff00 0x80ff007f 0x3210 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3211 = (0x7f80ffff : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3212 = (0x7f80ff80 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3213 = (0x7f80ff7f : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3214 = (0x7f80ff7f : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3215 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3216 = (0x7f80ffff : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3217 = (0x7f80ff80 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3218 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3219 = (0x7f80ffff : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x321a = (0x7f80ffff : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x321b = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x321c = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x321d = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x321e = (0x7f80ffff : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x321f = (0x7f80ffff : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3200 = (0x7f800000 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3210 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3220 = (0x7f808000 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3230 = (0x7f807f00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3240 = (0x7f807f00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3250 = (0x7f800000 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3260 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3270 = (0x7f808000 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3280 = (0x7f800000 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3290 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x32a0 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x32b0 = (0x7f800000 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x32c0 = (0x7f800000 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x32d0 = (0x7f800000 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x32e0 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x32f0 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3010 = (0x7f00ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3110 = (0x7fffff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3210 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3310 = (0x7f7fff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3410 = (0x7f7fff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3510 = (0x7f00ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3610 = (0x7fffff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3710 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3810 = (0x7f00ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3910 = (0x7fffff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3a10 = (0x7fffff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3b10 = (0x7f00ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3c10 = (0x7f00ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3d10 = (0x7f00ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3e10 = (0x7fffff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3f10 = (0x7fffff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x210 = (0x80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x1210 = (0xff80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x2210 = (0x8080ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x3210 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x4210 = (0x7f80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x5210 = (0x80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x6210 = (0xff80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x7210 = (0x8080ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x8210 = (0x80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0x9210 = (0xff80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0xa210 = (0xff80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0xb210 = (0x80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0xc210 = (0x80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0xd210 = (0x80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0xe210 = (0xff80ff00 : Word) := by decide
example : compute .permute 0x7f80ff00 0x80ff007f 0xf210 = (0xff80ff00 : Word) := by decide
end Ptx.Scalar.Prmt32.Acceptance
