import Ptx.Select32

/-! Coordinator-owned independent frozen acceptance checks. This file is not a
worker source file. Universal signatures and source-specific examples are distinct. -/
open Ptx Ptx.Scalar
namespace AcceptanceSelect32
open Ptx.Scalar.Select32

example (a b : Word) (c : Bool) :
    compute a b c = if c then a else b :=
  compute_eq a b c

example (op : Operation) (words : Fin 2 → Word) (predicates : Fin 1 → Bool) (value : Word) :
    family.Results op words predicates value ↔ value = if predicates 0 then words 0 else words 1 :=
  results_iff op words predicates value

example (i : Instr) :
    (lower i).operation = .selp ∧ (lower i).predicates 0 = .reg i.predicate true :=
  lower_predicate i

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
private def tested : Instr := ⟨.pred 3 true, 0, .reg 0, .reg 1, 3⟩
private def expected : Word := 0xffffffff
example : compute 0x80000000 7 true = 0x80000000 := by first | rfl | decide
example : compute 0x80000000 7 false = 7 := by first | rfl | decide
example : result tested incoming = 0xffffffff := by first | rfl | decide
-- The same predicate controls execution and selects the first incoming source.
example : (occurrence incoming tested true).reads =
    [.predicate 3, .word 0, .word 1, .predicate 3] := by first | rfl | decide
example : Text.decode ⟨.pred 3 false, "selp.b32",
    [.word (.reg 1), .word (.imm 0x80000000), .word (.reg 1), .predicate 3]⟩ =
    .ok (⟨.pred 3 false, 1, .imm 0x80000000, .reg 1, 3⟩ : Instr) := by rfl
example : Text.encode tested = ⟨.pred 3 true, "selp.b32",
    [.word (.reg 0), .word (.reg 0), .word (.reg 1), .predicate 3]⟩ := by rfl
-- Negated guard executes precisely when the selector is false, so it copies b.
private def neg : Instr := {tested with guard := .pred 2 false, predicate := 2}
example : result neg incoming = 7 := by first | rfl | decide
example : Eval neg incoming (Pure32.write incoming 0 7) (occurrence incoming neg true) := by
  apply (eval_true_iff neg incoming _ _ (by rfl)).mpr
  exact ⟨rfl, rfl⟩
private def repeated : Instr := {tested with left := .reg 0, right := .reg 0}
example : (occurrence incoming repeated true).reads =
    [.predicate 3, .word 0, .word 0, .predicate 3] := by first | rfl | decide

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

example : Text.supportedMnemonic "selp.b32" = true := by rfl
example : Text.decode ⟨.always, "selp.b32", []⟩ =
    .error (.invalidOperands "selp.b32") := by rfl
example : Text.decode ⟨.always, "selp.b32", [.word (.reg 0)]⟩ =
    .error (.invalidOperands "selp.b32") := by rfl
example : Text.decode ⟨.always, "selp.b32", [.word (.imm 0), .word (.reg 1), .word (.imm 7), .predicate 3]⟩ =
    .error (.invalidOperands "selp.b32") := by rfl
example : Text.decode ⟨.always, "selp.b32", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .word (.reg 3)]⟩ =
    .error (.invalidOperands "selp.b32") := by rfl
example : Text.decode ⟨.always, "selp.b32", [.word (.reg 0), .address (.reg 1), .word (.imm 7), .predicate 3]⟩ =
    .error (.invalidOperands "selp.b32") := by rfl
example : Text.decode ⟨.always, "selp.b32", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .predicate 3, .predicate 4]⟩ =
    .error (.invalidOperands "selp.b32") := by rfl

example : Text.supportedMnemonic "selp" = false := by rfl
example : Text.decode ⟨.always, "selp", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .predicate 3]⟩ =
    .error (.unsupportedMnemonic "selp") := by rfl
example : Text.decode ⟨.always, "selp", []⟩ =
    .error (.unsupportedMnemonic "selp") := by rfl

example : Text.supportedMnemonic "selp.u32" = false := by rfl
example : Text.decode ⟨.always, "selp.u32", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .predicate 3]⟩ =
    .error (.unsupportedMnemonic "selp.u32") := by rfl
example : Text.decode ⟨.always, "selp.u32", []⟩ =
    .error (.unsupportedMnemonic "selp.u32") := by rfl

example : Text.supportedMnemonic "selp.s32" = false := by rfl
example : Text.decode ⟨.always, "selp.s32", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .predicate 3]⟩ =
    .error (.unsupportedMnemonic "selp.s32") := by rfl
example : Text.decode ⟨.always, "selp.s32", []⟩ =
    .error (.unsupportedMnemonic "selp.s32") := by rfl

example : Text.supportedMnemonic "selp.b16" = false := by rfl
example : Text.decode ⟨.always, "selp.b16", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .predicate 3]⟩ =
    .error (.unsupportedMnemonic "selp.b16") := by rfl
example : Text.decode ⟨.always, "selp.b16", []⟩ =
    .error (.unsupportedMnemonic "selp.b16") := by rfl

example : Text.supportedMnemonic "selp.b64" = false := by rfl
example : Text.decode ⟨.always, "selp.b64", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .predicate 3]⟩ =
    .error (.unsupportedMnemonic "selp.b64") := by rfl
example : Text.decode ⟨.always, "selp.b64", []⟩ =
    .error (.unsupportedMnemonic "selp.b64") := by rfl

example : Text.supportedMnemonic "selp.f32" = false := by rfl
example : Text.decode ⟨.always, "selp.f32", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .predicate 3]⟩ =
    .error (.unsupportedMnemonic "selp.f32") := by rfl
example : Text.decode ⟨.always, "selp.f32", []⟩ =
    .error (.unsupportedMnemonic "selp.f32") := by rfl

example : Text.supportedMnemonic "selp.b32.ftz" = false := by rfl
example : Text.decode ⟨.always, "selp.b32.ftz", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .predicate 3]⟩ =
    .error (.unsupportedMnemonic "selp.b32.ftz") := by rfl
example : Text.decode ⟨.always, "selp.b32.ftz", []⟩ =
    .error (.unsupportedMnemonic "selp.b32.ftz") := by rfl

example : Text.supportedMnemonic "selp.ftz.b32" = false := by rfl
example : Text.decode ⟨.always, "selp.ftz.b32", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .predicate 3]⟩ =
    .error (.unsupportedMnemonic "selp.ftz.b32") := by rfl
example : Text.decode ⟨.always, "selp.ftz.b32", []⟩ =
    .error (.unsupportedMnemonic "selp.ftz.b32") := by rfl

example : Text.supportedMnemonic "selp.b32.extra" = false := by rfl
example : Text.decode ⟨.always, "selp.b32.extra", [.word (.reg 0), .word (.reg 1), .word (.imm 7), .predicate 3]⟩ =
    .error (.unsupportedMnemonic "selp.b32.extra") := by rfl
example : Text.decode ⟨.always, "selp.b32.extra", []⟩ =
    .error (.unsupportedMnemonic "selp.b32.extra") := by rfl

end AcceptanceSelect32
