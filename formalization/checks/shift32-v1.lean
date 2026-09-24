import Ptx.Shift32
open Ptx
namespace Ptx.Scalar.Shift32.Acceptance

example : ∀ (op : Operation) (a b : Word),
    compute op a b = match op with
      | .shl => if b.toNat < 32 then a <<< b.toNat else 0
      | .shrU => if b.toNat < 32 then a >>> b.toNat else 0
      | .shrS => if b.toNat < 32 then a.sshiftRight b.toNat
          else if a.msb then 0xffffffff else 0 :=
  @compute_eq

example : ∀ (op : Operation) (words : Fin 2 → Word) (predicates : Fin 0 → Bool) (value : Word),
    family.Results op words predicates value ↔ value = compute op (words 0) (words 1) :=
  @results_iff

example : ∀ (i : Instr),
    (lower i).operation = i.operation :=
  @lower_operation

example : ∀ (i : Instr),
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words (⟨0, by decide⟩ : Fin 2) = i.left ∧ (lower i).words (⟨1, by decide⟩ : Fin 2) = i.right :=
  @lower_fields

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true),
    Eval i s next event ↔
      next = Pure32.write s i.destination (result i s) ∧ event = occurrence s i true :=
  @eval_true_iff

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false),
    Eval i s next event ↔
      next = {s with pc := s.pc + 1} ∧ event = occurrence s i false :=
  @eval_false_iff

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) (enabled : i.guard.eval s = true),
    next.regs i.destination = result i s :=
  @eval_destination

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event),
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧
      next.addrs = s.addrs ∧ next.preds = s.preds :=
  @eval_frame

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (evaluated : Eval i s next event) (different : other ≠ i.destination),
    next.regs other = s.regs other :=
  @eval_other

example : ∀ (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event),
    event = occurrence s i (i.guard.eval s) :=
  @eval_event

example : ∀ (i : Instr) (s next₁ next₂ : Scalar.State) (event₁ event₂ : Occurrence)
    (left : Eval i s next₁ event₁) (right : Eval i s next₂ event₂),
    next₁ = next₂ ∧ event₁ = event₂ :=
  @eval_deterministic

example : ∀ (i : Instr) (s : Scalar.State),
    ∃ next event, Eval i s next event :=
  @eval_exists

example : ∀ (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (stepped : Step target program s next event),
    SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧
      event.pc = s.pc ∧ event.instruction = lower i ∧ Eval i s next event :=
  @step_origin

example : ∀ (target : Ptx.Target) (program : List Instr) (s : Scalar.State) (i : Instr)
    (supported : SupportedTarget target) (fetch : program[s.pc]? = some i),
    ∃ next event, Step target program s next event :=
  @step_exists

example : ∀ (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (missing : program[s.pc]? = none),
    ¬ Step target program s next event :=
  @step_no_fetch

example : ∀ (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (unsupported : ¬ SupportedTarget target),
    ¬ Step target program s next event :=
  @step_unsupported_target

example : ∀ (i : Instr),
    Text.decode (Text.encode i) = .ok i :=
  @Text.decode_encode

example : ∀ (statement : Scalar.Text.Statement) (i : Instr),
    Text.decode statement = .ok i ↔ statement = Text.encode i :=
  @Text.decode_iff

example : compute .shl 1 0 = 1 := by decide
example : compute .shl 1 31 = 2147483648 := by decide
example : compute .shl 1 32 = 0 := by decide
example : compute .shl 1 33 = 0 := by decide
example : compute .shl 1 4294967295 = 0 := by decide
example : compute .shrU 2147483648 1 = 1073741824 := by decide
example : compute .shrU 4294967295 31 = 1 := by decide
example : compute .shrU 4294967295 32 = 0 := by decide
example : compute .shrU 4294967295 4294967295 = 0 := by decide
example : compute .shrS 2147483648 1 = 3221225472 := by decide
example : compute .shrS 2147483648 31 = 4294967295 := by decide
example : compute .shrS 2147483648 32 = 4294967295 := by decide
example : compute .shrS 2147483648 4294967295 = 4294967295 := by decide
example : compute .shrS 2147483647 32 = 0 := by decide
example : compute .shrS 0 33 = 0 := by decide
private def incoming : Scalar.State := ⟨7, fun r => if r = 0 then 0x80000000 else 1, fun _ => 0, fun _ => true, [11,22]⟩
private def tested : Instr := ⟨.pred 3 true, .shrS, 0, .reg 0, .reg 0⟩
example : result tested incoming = 0xffffffff := by decide
example : (occurrence incoming tested true).reads = [.predicate 3, .word 0, .word 0] := by rfl
example : Eval tested incoming (Pure32.write incoming 0 0xffffffff) (occurrence incoming tested true) :=
  (eval_true_iff tested incoming _ _ (by rfl)).mpr ⟨by decide, rfl⟩
private def skipped : Instr := {tested with guard := .pred 3 false}
example : Eval skipped incoming {incoming with pc := 8} (occurrence incoming skipped false) :=
  (eval_false_iff skipped incoming _ _ (by rfl)).mpr ⟨rfl,rfl⟩
example : (occurrence incoming skipped false).reads = [.predicate 3] := by rfl
example : SupportedTarget ⟨94,10⟩ := by constructor <;> decide
example : ¬ SupportedTarget ⟨93,90⟩ := by intro h; have := h.1; contradiction
example : ¬ SupportedTarget ⟨94,9⟩ := by intro h; have : (10 : Nat) ≤ 9 := h.2; omega
example : Text.decode ⟨.pred 3 false, "shl.b32", [.word (.reg 0), .word (.reg 0), .word (.imm 33)]⟩ = .ok (⟨.pred 3 false, .shl, 0, .reg 0, .imm 33⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "shl.b32", []⟩ = .error (.invalidOperands "shl.b32") := by rfl
example : Text.decode ⟨.always, "shl.b32", [.word (.imm 0), .word (.reg 0), .word (.reg 1)]⟩ = .error (.invalidOperands "shl.b32") := by rfl
example : Text.decode ⟨.pred 3 false, "shr.u32", [.word (.reg 0), .word (.reg 0), .word (.imm 33)]⟩ = .ok (⟨.pred 3 false, .shrU, 0, .reg 0, .imm 33⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "shr.u32", []⟩ = .error (.invalidOperands "shr.u32") := by rfl
example : Text.decode ⟨.always, "shr.u32", [.word (.imm 0), .word (.reg 0), .word (.reg 1)]⟩ = .error (.invalidOperands "shr.u32") := by rfl
example : Text.decode ⟨.pred 3 false, "shr.s32", [.word (.reg 0), .word (.reg 0), .word (.imm 33)]⟩ = .ok (⟨.pred 3 false, .shrS, 0, .reg 0, .imm 33⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "shr.s32", []⟩ = .error (.invalidOperands "shr.s32") := by rfl
example : Text.decode ⟨.always, "shr.s32", [.word (.imm 0), .word (.reg 0), .word (.reg 1)]⟩ = .error (.invalidOperands "shr.s32") := by rfl
example : Text.decode ⟨.always, "shl.b64", []⟩ = .error (.unsupportedMnemonic "shl.b64") := by rfl
example : Text.decode ⟨.always, "shl.u32", []⟩ = .error (.unsupportedMnemonic "shl.u32") := by rfl
example : Text.decode ⟨.always, "shr.b32", []⟩ = .error (.unsupportedMnemonic "shr.b32") := by rfl
example : Text.decode ⟨.always, "shr.s64", []⟩ = .error (.unsupportedMnemonic "shr.s64") := by rfl
example : Text.decode ⟨.always, "unknown", []⟩ = .error (.unsupportedMnemonic "unknown") := by rfl
end Ptx.Scalar.Shift32.Acceptance
