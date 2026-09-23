import Ptx.IntegerMinMax

/-!
Coordinator-owned acceptance checks, prepared from the task and pinned source
before inspecting the worker implementation. Run in the candidate checkout with
`lake env lean /absolute/path/to/this/file`. `decide` is kernel checked; this file
uses neither `native_decide` nor an external expected-results oracle.

Universal signatures prevent extra input-domain assumptions. Independent examples
exercise actual evaluator and decoder behavior. These checks do not establish
source fidelity, hardware conformance, or completeness of the task's additional
algebraic proofs; those require the separate semantic and proof review.
-/
namespace Ptx.Scalar.IntegerMinMaxAcceptance

-- Let negative decoder probes reduce to false rather than fail instance synthesis.
deriving instance DecidableEq for Except
set_option synthInstance.maxSize 4096

-- Deliberately demand the exact public contract, without extra premises.
theorem min_signature : ∀ a b : Word,
    (BinOp.eval .minU a b).toNat = Nat.min a.toNat b.toNat :=
  IntegerMinMax.min_toNat

theorem max_signature : ∀ a b : Word,
    (BinOp.eval .maxU a b).toNat = Nat.max a.toNat b.toNat :=
  IntegerMinMax.max_toNat

-- Independent concrete semantics, without invoking either worker theorem.
example : BinOp.eval .minU 0xffffffff 0 = 0 ∧
    BinOp.eval .maxU 0xffffffff 0 = 0xffffffff := by first | rfl | decide
example : BinOp.eval .minU 0x80000000 0x7fffffff = 0x7fffffff ∧
    BinOp.eval .maxU 0x80000000 0x7fffffff = 0x80000000 := by first | rfl | decide
example : BinOp.eval .minU 7 11 = 7 ∧ BinOp.eval .minU 11 7 = 7 ∧
    BinOp.eval .maxU 7 11 = 11 ∧ BinOp.eval .maxU 11 7 = 11 := by first | rfl | decide
example : BinOp.eval .minU 0 0 = 0 ∧ BinOp.eval .maxU 0 0 = 0 ∧
    BinOp.eval .minU 0xffffffff 0xffffffff = 0xffffffff ∧
    BinOp.eval .maxU 0xffffffff 0xffffffff = 0xffffffff := by first | rfl | decide

-- This independent structural contract is stronger than finitely sampled frames:
-- all non-destination registers, addresses, predicates and memory stay unchanged.
-- Operand evaluation explicitly uses the incoming state, including overlap.
theorem actual_eval_frame (s : State) (operation : BinOp) (destination : Nat)
    (left right : Operand32) (guard : Guard) (h : guard.eval s = true)
    (readOverride : Option Word) :
    eval readOverride ⟨guard, .bin32 operation destination left right⟩ s =
      .next {s with pc := s.pc + 1, regs := update s.regs destination (operation.eval (left.eval s) (right.eval s))}
        (occurrence s ⟨guard, .bin32 operation destination left right⟩ true) := by
  simp [eval, h]

theorem actual_eval_skipped (s : State) (operation : BinOp) (destination : Nat)
    (left right : Operand32) (guard : Guard) (h : guard.eval s = false)
    (readOverride : Option Word) :
    eval readOverride ⟨guard, .bin32 operation destination left right⟩ s =
      .next {s with pc := s.pc + 1}
        (occurrence s ⟨guard, .bin32 operation destination left right⟩ false) := by
  simp [eval, h]

private def initial : State :=
  { pc := 9
    regs := fun i => if i = 0 then 0x80000000 else if i = 1 then 7 else 99
    addrs := fun _ => 0x1000
    preds := fun i => i = 1
    memory := [3, 5] }

-- A finite observation of the actual step permits computation without deciding
-- equality of whole register functions. The universal frame check above supplies
-- the corresponding unsampled guarantee.
private def observation (result : StepResult) :
    Option (Nat × Word × Word × Word × Address × Bool × List Word × Occurrence) :=
  match result with
  | .next s event => some (s.pc, s.regs 0, s.regs 1, s.regs 2,
      s.addrs 0, s.preds 1, s.memory, event)
  | _ => none

private def expected (instruction : Instr) (executed : Bool)
    (r0 r1 : Word) :
    Option (Nat × Word × Word × Word × Address × Bool × List Word × Occurrence) :=
  some (10, r0, r1, 99, 0x1000, true, [3, 5],
    ⟨9, instruction, executed,
      instruction.guard.reads ++ if executed then instruction.op.reads else [],
      if executed then [.word (match instruction.op with
        | .bin32 _ d _ _ => d | _ => 0)] else [], none⟩)

-- Both source/destination overlap positions, for both operations. The selected
-- results include cases where the destination must actually change.
example : observation (eval none (.plain (.bin32 .minU 0 (.reg 0) (.reg 1))) initial) =
    expected (.plain (.bin32 .minU 0 (.reg 0) (.reg 1))) true 7 7 := by first | rfl | decide
example : observation (eval none (.plain (.bin32 .minU 0 (.reg 1) (.reg 0))) initial) =
    expected (.plain (.bin32 .minU 0 (.reg 1) (.reg 0))) true 7 7 := by first | rfl | decide
example : observation (eval none (.plain (.bin32 .maxU 1 (.reg 1) (.reg 0))) initial) =
    expected (.plain (.bin32 .maxU 1 (.reg 1) (.reg 0))) true 0x80000000 0x80000000 := by first | rfl | decide
example : observation (eval none (.plain (.bin32 .maxU 1 (.reg 0) (.reg 1))) initial) =
    expected (.plain (.bin32 .maxU 1 (.reg 0) (.reg 1))) true 0x80000000 0x80000000 := by first | rfl | decide

-- p0 is false and p1 is true: @p0 and @!p1 both skip an otherwise changing write.
example : observation (eval none ⟨.pred 0 true, .bin32 .minU 0 (.reg 0) (.reg 1)⟩ initial) =
    expected ⟨.pred 0 true, .bin32 .minU 0 (.reg 0) (.reg 1)⟩ false 0x80000000 7 := by first | rfl | decide
example : observation (eval none ⟨.pred 1 false, .bin32 .maxU 1 (.reg 0) (.reg 1)⟩ initial) =
    expected ⟨.pred 1 false, .bin32 .maxU 1 (.reg 0) (.reg 1)⟩ false 0x80000000 7 := by first | rfl | decide

-- Direct read metadata must include both actual source registers and guard.
example : (occurrence initial (.plain (.bin32 .minU 0 (.reg 0) (.reg 1))) true).reads =
    [.word 0, .word 1] := by first | rfl | decide
example : (occurrence initial ⟨.pred 1 true, .bin32 .maxU 0 (.imm 7) (.reg 1)⟩ true).reads =
    [.predicate 1, .word 1] := by first | rfl | decide
example : (occurrence initial ⟨.pred 0 true, .bin32 .minU 0 (.reg 0) (.reg 1)⟩ false).reads =
    [.predicate 0] := by first | rfl | decide

open Text

example : decode ⟨.pred 1 false, "min.u32", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ =
    .ok ⟨.pred 1 false, .bin32 .minU 0 (.reg 1) (.imm 7)⟩ := by first | rfl | decide
example : decodeOp "max.u32" [.word (.reg 0), .word (.imm 0xffffffff), .word (.reg 1)] =
    .ok (.bin32 .maxU 0 (.imm 0xffffffff) (.reg 1)) := by first | rfl | decide
example : encode (.plain (.bin32 .minU 0 (.reg 1) (.imm 7))) =
    ⟨.always, "min.u32", [.word (.reg 0), .word (.reg 1), .word (.imm 7)]⟩ := by first | rfl | decide
example : encode (.plain (.bin32 .maxU 0 (.imm 7) (.reg 1))) =
    ⟨.always, "max.u32", [.word (.reg 0), .word (.imm 7), .word (.reg 1)]⟩ := by first | rfl | decide

-- Supported mnemonic but malformed operand categories/arity must report that
-- distinction; unsupported forms must not become aliases for these two forms.
example : decodeOp "min.u32" [.word (.imm 0), .word (.reg 1), .word (.imm 7)] =
    .error (.invalidOperands "min.u32") := by first | rfl | decide
example : decodeOp "max.u32" [.word (.reg 0), .address (.reg 1), .word (.imm 7)] =
    .error (.invalidOperands "max.u32") := by first | rfl | decide
example : decodeOp "min.u32" [.word (.reg 0), .word (.reg 1)] =
    .error (.invalidOperands "min.u32") := by first | rfl | decide
example : decodeOp "max.u32" [.word (.reg 0), .word (.reg 1), .word (.imm 7), .word (.imm 8)] =
    .error (.invalidOperands "max.u32") := by first | rfl | decide
example : decodeOp "min.relu.u32" [.word (.reg 0), .word (.reg 1), .word (.imm 7)] =
    .error (.unsupportedMnemonic "min.relu.u32") := by first | rfl | decide
example : decodeOp "max.s32" [.word (.reg 0), .word (.reg 1), .word (.imm 7)] =
    .error (.unsupportedMnemonic "max.s32") := by first | rfl | decide
example : decodeOp "min.u64" [.word (.reg 0), .word (.reg 1), .word (.imm 7)] =
    .error (.unsupportedMnemonic "min.u64") := by first | rfl | decide
example : decodeOp "max.u16x2" [.word (.reg 0), .word (.reg 1), .word (.imm 7)] =
    .error (.unsupportedMnemonic "max.u16x2") := by first | rfl | decide

#print axioms min_signature
#print axioms max_signature
#print axioms actual_eval_frame
#print axioms actual_eval_skipped
#print axioms Text.decode_encode
#print axioms Text.decodeOp_supported

end Ptx.Scalar.IntegerMinMaxAcceptance
