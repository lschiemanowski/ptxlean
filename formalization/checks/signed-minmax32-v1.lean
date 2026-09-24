import Ptx.SignedMinMax32

/-! Coordinator-owned independent frozen acceptance checks. This file is not a
worker source file. Universal signatures and source-specific examples are distinct. -/
open Ptx Ptx.Scalar
namespace AcceptanceSignedMinMax32
open Ptx.Scalar.SignedMinMax32

example (a b : Word) :
    compute .min a b = if a.toInt < b.toInt then a else b :=
  compute_min a b

example (a b : Word) :
    compute .max a b = if a.toInt > b.toInt then a else b :=
  compute_max a b

example (op : Operation) (a b : Word) :
    (compute op a b).toInt = match op with
      | .min => min a.toInt b.toInt
      | .max => max a.toInt b.toInt :=
  compute_toInt op a b

example (op : Operation) (words : Fin 2 → Word) (predicates : Fin 0 → Bool) (value : Word) :
    family.Results op words predicates value ↔ value = compute op (words 0) (words 1) :=
  results_iff op words predicates value

example (i : Instr) :
    (lower i).operation = i.operation :=
  lower_operation i

example (i : Instr) :
    (lower i).guard = i.guard ∧ (lower i).destination = i.destination ∧
    (lower i).words 0 = i.left ∧ (lower i).words 1 = i.right :=
  lower_fields i

example (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (enabled : i.guard.eval s = true) :
    Eval i s next event ↔
      next = Pure32.write s i.destination (result i s) ∧ event = occurrence s i true :=
  eval_true_iff i s next event enabled

example (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (disabled : i.guard.eval s = false) :
    Eval i s next event ↔
      next = {s with pc := s.pc + 1} ∧ event = occurrence s i false :=
  eval_false_iff i s next event disabled

example (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) (enabled : i.guard.eval s = true) :
    next.regs i.destination = result i s :=
  eval_destination i s next event evaluated enabled

example (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) :
    next.pc = s.pc + 1 ∧ next.memory = s.memory ∧
      next.addrs = s.addrs ∧ next.preds = s.preds :=
  eval_frame i s next event evaluated

example (i : Instr) (s next : Scalar.State) (event : Occurrence) (other : Nat)
    (evaluated : Eval i s next event) (different : other ≠ i.destination) :
    next.regs other = s.regs other :=
  eval_other i s next event other evaluated different

example (i : Instr) (s next : Scalar.State) (event : Occurrence)
    (evaluated : Eval i s next event) :
    event = occurrence s i (i.guard.eval s) :=
  eval_event i s next event evaluated

example (i : Instr) (s next₁ next₂ : Scalar.State) (event₁ event₂ : Occurrence)
    (left : Eval i s next₁ event₁) (right : Eval i s next₂ event₂) :
    next₁ = next₂ ∧ event₁ = event₂ :=
  eval_deterministic i s next₁ next₂ event₁ event₂ left right

example (i : Instr) (s : Scalar.State) :
    ∃ next event, Eval i s next event :=
  eval_exists i s

example (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (stepped : Step target program s next event) :
    SupportedTarget target ∧ ∃ i, program[s.pc]? = some i ∧
      event.pc = s.pc ∧ event.instruction = lower i ∧ Eval i s next event :=
  step_origin target program s next event stepped

example (target : Ptx.Target) (program : List Instr) (s : Scalar.State) (i : Instr)
    (supported : SupportedTarget target) (fetch : program[s.pc]? = some i) :
    ∃ next event, Step target program s next event :=
  step_exists target program s i supported fetch

example (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (missing : program[s.pc]? = none) :
    ¬ Step target program s next event :=
  step_no_fetch target program s next event missing

example (target : Ptx.Target) (program : List Instr)
    (s next : Scalar.State) (event : Occurrence) (unsupported : ¬ SupportedTarget target) :
    ¬ Step target program s next event :=
  step_unsupported_target target program s next event unsupported

example (i : Instr) :
    Text.decode (Text.encode i) = .ok i :=
  Text.decode_encode i

example (statement : Scalar.Text.Statement) (i : Instr) :
    Text.decode statement = .ok i ↔ statement = Text.encode i :=
  Text.decode_iff statement i


-- A nonzero PC and nontrivial register/memory banks detect accidental resets.
private def incoming : Scalar.State :=
  ⟨2, fun r => if r = 0 then 0xffffffff else if r = 1 then 7 else 99,
    fun r => BitVec.ofNat 64 (100 + r), fun r => r == 3, [11, 22, 33]⟩
private def tested : Instr := ⟨.pred 3 true, .min, 0, .reg 0, .reg 1⟩
private def expected : Word := 0xffffffff
example : compute .min 0xffffffff 7 = 0xffffffff := by first | rfl | decide
example : compute .max 0xffffffff 7 = 7 := by first | rfl | decide
example : compute .min 0x80000000 0x7fffffff = 0x80000000 := by first | rfl | decide
example : compute .max 0x80000000 0x7fffffff = 0x7fffffff := by first | rfl | decide
example : compute .min 0x80000000 0xffffffff = 0x80000000 := by first | rfl | decide
example : compute .max 0x80000000 0xffffffff = 0xffffffff := by first | rfl | decide
example : compute .min 0xffffffff 0xffffffff = 0xffffffff := by first | rfl | decide
example : compute .max 0 0 = 0 := by first | rfl | decide
example : result tested incoming = 0xffffffff := by first | rfl | decide
example : (occurrence incoming tested true).reads =
    [.predicate 3, .word 0, .word 1] := by first | rfl | decide
example : Text.decode ⟨.pred 3 false, "min.s32",
    [.word (.reg 1), .word (.imm 0x80000000), .word (.reg 1)]⟩ =
    .ok (⟨.pred 3 false, .min, 1, .imm 0x80000000, .reg 1⟩ : Instr) := by rfl
example : Text.decode ⟨.always, "max.s32",
    [.word (.reg 1), .word (.reg 1), .word (.imm 0xffffffff)]⟩ =
    .ok (⟨.always, .max, 1, .reg 1, .imm 0xffffffff⟩ : Instr) := by rfl
example : Text.encode tested = ⟨.pred 3 true, "min.s32",
    [.word (.reg 0), .word (.reg 0), .word (.reg 1)]⟩ := by rfl
example : Text.encode {tested with operation := .max} = ⟨.pred 3 true, "max.s32",
    [.word (.reg 0), .word (.reg 0), .word (.reg 1)]⟩ := by rfl
private def neg : Instr := {tested with guard := .pred 2 false, operation := .max}
example : Eval neg incoming (Pure32.write incoming 0 7) (occurrence incoming neg true) := by
  apply (eval_true_iff neg incoming _ _ (by rfl)).mpr
  exact ⟨rfl, rfl⟩
private def repeated : Instr := {tested with left := .reg 0, right := .reg 0}
example : (occurrence incoming repeated true).reads =
    [.predicate 3, .word 0, .word 0] := by first | rfl | decide

example : Eval tested incoming (Pure32.write incoming 0 expected)
    (occurrence incoming tested true) := by
  apply (eval_true_iff tested incoming _ _ (by rfl)).mpr
  exact ⟨rfl, rfl⟩
-- Every source names the destination; reading after writing is not allowed.
example : Eval repeated incoming (Pure32.write incoming 0 0xffffffff)
    (occurrence incoming repeated true) := by
  apply (eval_true_iff repeated incoming _ _ (by rfl)).mpr
  exact ⟨rfl, rfl⟩
-- Right-only alias, with different source values.
private def rightAlias : Instr := {tested with destination := 1}
example : Eval rightAlias incoming (Pure32.write incoming 1 expected)
    (occurrence incoming rightAlias true) := by
  apply (eval_true_iff rightAlias incoming _ _ (by rfl)).mpr
  exact ⟨rfl, rfl⟩
example : (occurrence incoming tested true).writes = [.word 0] := by rfl
example : (occurrence incoming tested true).memory = none := by rfl
example : (occurrence incoming tested true).pc = 2 := by rfl
example : (occurrence incoming tested true).instruction = lower tested := by rfl
private def skippedPositive : Instr := {tested with guard := .pred 2 true}
private def skippedNegative : Instr := {tested with guard := .pred 3 false}
example : Eval skippedPositive incoming {incoming with pc := 3}
    (occurrence incoming skippedPositive false) := by
  apply (eval_false_iff skippedPositive incoming _ _ (by rfl)).mpr
  exact ⟨rfl, rfl⟩
example : Eval skippedNegative incoming {incoming with pc := 3}
    (occurrence incoming skippedNegative false) := by
  apply (eval_false_iff skippedNegative incoming _ _ (by rfl)).mpr
  exact ⟨rfl, rfl⟩
example : (occurrence incoming skippedPositive false).reads = [.predicate 2] := by rfl
example : (occurrence incoming skippedNegative false).reads = [.predicate 3] := by rfl
example : (occurrence incoming skippedNegative false).writes = [] := by rfl
example : (occurrence incoming skippedNegative false).memory = none := by rfl
example : SupportedTarget ⟨94,10⟩ := by decide
example : SupportedTarget ⟨94,90⟩ := by decide
example : ¬ SupportedTarget ⟨93,90⟩ := by decide
example : ¬ SupportedTarget ⟨95,90⟩ := by decide
example : ¬ SupportedTarget ⟨94,9⟩ := by decide
-- Genuine fetch at PC2, with a different instruction in the first two slots.
example : Step ⟨94,10⟩ [neg, neg, tested] incoming
    (Pure32.write incoming 0 expected) (occurrence incoming tested true) := by
  exact ⟨lower tested, rfl, by decide,
    (eval_true_iff tested incoming _ _ (by rfl)).mpr ⟨rfl, rfl⟩⟩
example (next : Scalar.State) (event : Occurrence) :
    ¬ Step ⟨94,90⟩ [tested] incoming next event :=
  step_no_fetch _ _ _ _ _ rfl
-- Unsupported target remains rejected even when the fetched guard is false.
example (next : Scalar.State) (event : Occurrence) :
    ¬ Step ⟨94,9⟩ [neg, neg, skippedNegative] incoming next event :=
  step_unsupported_target _ _ _ _ _ (by decide)
example (next : Scalar.State) (event : Occurrence) :
    ¬ Step ⟨93,90⟩ [neg, neg, tested] incoming next event :=
  step_unsupported_target _ _ _ _ _ (by decide)

example : Text.supportedMnemonic "min.s32" = true := by rfl
example : Text.decode ⟨.always, "min.s32", []⟩ =
    .error (.invalidOperands "min.s32") := by rfl
example : Text.decode ⟨.always, "min.s32", [.word (.reg 0)]⟩ =
    .error (.invalidOperands "min.s32") := by rfl
example : Text.decode ⟨.always, "min.s32", [.word (.imm 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.invalidOperands "min.s32") := by rfl
example : Text.decode ⟨.always, "min.s32", [.word (.reg 0), .word (.reg 1), .predicate 3]⟩ =
    .error (.invalidOperands "min.s32") := by rfl
example : Text.decode ⟨.always, "min.s32", [.word (.reg 0), .memory (.reg 1), .word (.imm 7)]⟩ =
    .error (.invalidOperands "min.s32") := by rfl
example : Text.decode ⟨.always, "min.s32", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .word (.imm 8)]⟩ =
    .error (.invalidOperands "min.s32") := by rfl

example : Text.supportedMnemonic "max.s32" = true := by rfl
example : Text.decode ⟨.always, "max.s32", []⟩ =
    .error (.invalidOperands "max.s32") := by rfl
example : Text.decode ⟨.always, "max.s32", [.word (.reg 0)]⟩ =
    .error (.invalidOperands "max.s32") := by rfl
example : Text.decode ⟨.always, "max.s32", [.word (.imm 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.invalidOperands "max.s32") := by rfl
example : Text.decode ⟨.always, "max.s32", [.word (.reg 0), .word (.reg 1), .predicate 3]⟩ =
    .error (.invalidOperands "max.s32") := by rfl
example : Text.decode ⟨.always, "max.s32", [.word (.reg 0), .memory (.reg 1), .word (.imm 7)]⟩ =
    .error (.invalidOperands "max.s32") := by rfl
example : Text.decode ⟨.always, "max.s32", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .word (.imm 8)]⟩ =
    .error (.invalidOperands "max.s32") := by rfl

example : Text.supportedMnemonic "min" = false := by rfl
example : Text.decode ⟨.always, "min", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "min") := by rfl
example : Text.decode ⟨.always, "min", []⟩ =
    .error (.unsupportedMnemonic "min") := by rfl

example : Text.supportedMnemonic "max" = false := by rfl
example : Text.decode ⟨.always, "max", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "max") := by rfl
example : Text.decode ⟨.always, "max", []⟩ =
    .error (.unsupportedMnemonic "max") := by rfl

example : Text.supportedMnemonic "min.u32" = false := by rfl
example : Text.decode ⟨.always, "min.u32", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "min.u32") := by rfl
example : Text.decode ⟨.always, "min.u32", []⟩ =
    .error (.unsupportedMnemonic "min.u32") := by rfl

example : Text.supportedMnemonic "max.u32" = false := by rfl
example : Text.decode ⟨.always, "max.u32", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "max.u32") := by rfl
example : Text.decode ⟨.always, "max.u32", []⟩ =
    .error (.unsupportedMnemonic "max.u32") := by rfl

example : Text.supportedMnemonic "min.s64" = false := by rfl
example : Text.decode ⟨.always, "min.s64", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "min.s64") := by rfl
example : Text.decode ⟨.always, "min.s64", []⟩ =
    .error (.unsupportedMnemonic "min.s64") := by rfl

example : Text.supportedMnemonic "max.s16" = false := by rfl
example : Text.decode ⟨.always, "max.s16", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "max.s16") := by rfl
example : Text.decode ⟨.always, "max.s16", []⟩ =
    .error (.unsupportedMnemonic "max.s16") := by rfl

example : Text.supportedMnemonic "min.relu.s32" = false := by rfl
example : Text.decode ⟨.always, "min.relu.s32", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "min.relu.s32") := by rfl
example : Text.decode ⟨.always, "min.relu.s32", []⟩ =
    .error (.unsupportedMnemonic "min.relu.s32") := by rfl

example : Text.supportedMnemonic "max.relu.s32" = false := by rfl
example : Text.decode ⟨.always, "max.relu.s32", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "max.relu.s32") := by rfl
example : Text.decode ⟨.always, "max.relu.s32", []⟩ =
    .error (.unsupportedMnemonic "max.relu.s32") := by rfl

example : Text.supportedMnemonic "min.s32.relu" = false := by rfl
example : Text.decode ⟨.always, "min.s32.relu", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "min.s32.relu") := by rfl
example : Text.decode ⟨.always, "min.s32.relu", []⟩ =
    .error (.unsupportedMnemonic "min.s32.relu") := by rfl

example : Text.supportedMnemonic "max.s32.extra" = false := by rfl
example : Text.decode ⟨.always, "max.s32.extra", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "max.s32.extra") := by rfl
example : Text.decode ⟨.always, "max.s32.extra", []⟩ =
    .error (.unsupportedMnemonic "max.s32.extra") := by rfl

example : Text.supportedMnemonic "min.s16x2" = false := by rfl
example : Text.decode ⟨.always, "min.s16x2", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "min.s16x2") := by rfl
example : Text.decode ⟨.always, "min.s16x2", []⟩ =
    .error (.unsupportedMnemonic "min.s16x2") := by rfl

example : Text.supportedMnemonic "max.s8x4" = false := by rfl
example : Text.decode ⟨.always, "max.s8x4", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .error (.unsupportedMnemonic "max.s8x4") := by rfl
example : Text.decode ⟨.always, "max.s8x4", []⟩ =
    .error (.unsupportedMnemonic "max.s8x4") := by rfl

end AcceptanceSignedMinMax32
