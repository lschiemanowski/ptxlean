import Ptx.UnaryBits32
open Ptx
namespace Ptx.Scalar.UnaryBits32.Acceptance

example : ∀ (op : Operation) (a : Word),
    compute op a = match op with
      | .bitNot => ~~~a
      | .cnot => if a = 0 then 1 else 0 :=
  @compute_eq

example : ∀ (op : Operation) (words : Fin 1 → Word) (predicates : Fin 0 → Bool) (value : Word),
    family.Results op words predicates value ↔ value = compute op (words 0) :=
  @results_iff

example : ∀ (i : Instr),
    (lower i).operation = i.operation :=
  @lower_operation

example : ∀ (i : Instr),
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words 0 = i.source :=
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

example : compute .bitNot 0 = 0xffffffff := by decide
example : compute .bitNot 0x80000000 = 0x7fffffff := by decide
example : compute .cnot 0 = 1 := by decide
example : compute .cnot 2 = 0 := by decide
example : compute .cnot 0x80000000 = 0 := by decide
private def incoming : Scalar.State :=
  ⟨2, fun r => if r = 0 then 0x80000000 else 1,
    fun r => BitVec.ofNat 64 (100 + r), fun r => r == 3, [11, 22]⟩
private def tested : Instr := ⟨.pred 3 true, .bitNot, 0, .reg 0⟩
private def expected : Word := 0x7fffffff
example : result tested incoming = expected := by decide
example : (occurrence incoming tested true).reads = [.predicate 3, .word 0] := by rfl
example : Eval tested incoming (Pure32.write incoming 0 expected) (occurrence incoming tested true) := by
  apply (eval_true_iff tested incoming _ _ (by rfl)).mpr
  exact ⟨rfl, rfl⟩
private def skipped : Instr := {tested with guard := .pred 3 false}
example : Eval skipped incoming {incoming with pc := 3} (occurrence incoming skipped false) := by
  apply (eval_false_iff skipped incoming _ _ (by rfl)).mpr
  exact ⟨rfl, rfl⟩
example : (occurrence incoming skipped false).reads = [.predicate 3] := by rfl
example : (occurrence incoming skipped false).writes = [] := by rfl
example : (occurrence incoming tested true).memory = none := by rfl
example : SupportedTarget ⟨94,10⟩ := by constructor <;> decide
example : ¬ SupportedTarget ⟨93,90⟩ := by intro h; have := h.1; contradiction
example : ¬ SupportedTarget ⟨94,9⟩ := by intro h; have := h.2; omega
example : Step ⟨94,10⟩ [skipped, skipped, tested] incoming
    (Pure32.write incoming 0 expected) (occurrence incoming tested true) := by
  exact ⟨lower tested, rfl, by constructor <;> decide,
    (eval_true_iff tested incoming _ _ (by rfl)).mpr ⟨rfl, rfl⟩⟩
example : Text.decode ⟨.pred 3 false, "not.b32", [.word (.reg 0), .word (.reg 0)]⟩ = .ok (⟨.pred 3 false, .bitNot, 0, .reg 0⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "not.b32", []⟩ = .error (.invalidOperands "not.b32") := by rfl
example : Text.decode ⟨.always, "not.b32", [.word (.imm 0), .word (.reg 0)]⟩ = .error (.invalidOperands "not.b32") := by rfl
example : Text.decode ⟨.always, "not.b32", [.word (.reg 0), .predicate 1]⟩ = .error (.invalidOperands "not.b32") := by rfl
example : Text.decode ⟨.pred 3 false, "cnot.b32", [.word (.reg 0), .word (.reg 0)]⟩ = .ok (⟨.pred 3 false, .cnot, 0, .reg 0⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "cnot.b32", []⟩ = .error (.invalidOperands "cnot.b32") := by rfl
example : Text.decode ⟨.always, "cnot.b32", [.word (.imm 0), .word (.reg 0)]⟩ = .error (.invalidOperands "cnot.b32") := by rfl
example : Text.decode ⟨.always, "cnot.b32", [.word (.reg 0), .predicate 1]⟩ = .error (.invalidOperands "cnot.b32") := by rfl
example : Text.decode ⟨.always, "and.b64", []⟩ = .error (.unsupportedMnemonic "and.b64") := by rfl
example : Text.decode ⟨.always, "not.pred", []⟩ = .error (.unsupportedMnemonic "not.pred") := by rfl
example : Text.decode ⟨.always, "cnot.pred", []⟩ = .error (.unsupportedMnemonic "cnot.pred") := by rfl
example : Text.decode ⟨.always, "xor.u32", []⟩ = .error (.unsupportedMnemonic "xor.u32") := by rfl
example : Text.decode ⟨.always, "unsupported", []⟩ = .error (.unsupportedMnemonic "unsupported") := by rfl
end Ptx.Scalar.UnaryBits32.Acceptance
