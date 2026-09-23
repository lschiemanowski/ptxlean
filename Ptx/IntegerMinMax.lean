import Ptx.ScalarText

/-! Proofs and boundary examples for the two unsigned 32-bit min/max forms. -/
namespace Ptx.Scalar.IntegerMinMax

open Ptx.Scalar
open Ptx.Scalar.Text

theorem min_toNat (a b : Word) : (BinOp.eval .minU a b).toNat = Nat.min a.toNat b.toNat := by
  by_cases h : a.toNat ≤ b.toNat <;> simp [BinOp.eval, h, Nat.min_def]

theorem max_toNat (a b : Word) : (BinOp.eval .maxU a b).toNat = Nat.max a.toNat b.toNat := by
  by_cases h : b.toNat ≤ a.toNat <;> simp [BinOp.eval, h, Nat.le_of_not_ge]

theorem min_mem (a b : Word) : BinOp.eval .minU a b = a ∨ BinOp.eval .minU a b = b := by
  by_cases h : a.toNat ≤ b.toNat
  · simp [BinOp.eval, h]
  · simp [BinOp.eval, h]

theorem max_mem (a b : Word) : BinOp.eval .maxU a b = a ∨ BinOp.eval .maxU a b = b := by
  by_cases h : b.toNat ≤ a.toNat
  · simp [BinOp.eval, h]
  · simp [BinOp.eval, h]

theorem min_comm (a b : Word) : BinOp.eval .minU a b = BinOp.eval .minU b a := by
  apply BitVec.toNat_inj.mp
  simp [min_toNat, Nat.min_comm]

theorem max_comm (a b : Word) : BinOp.eval .maxU a b = BinOp.eval .maxU b a := by
  apply BitVec.toNat_inj.mp
  simp [max_toNat, Nat.max_comm]

theorem min_idem (a : Word) : BinOp.eval .minU a a = a := by
  unfold BinOp.eval
  simp

theorem max_idem (a : Word) : BinOp.eval .maxU a a = a := by
  unfold BinOp.eval
  simp

theorem min_bounds (a b : Word) :
    (BinOp.eval .minU a b).toNat ≤ a.toNat ∧ (BinOp.eval .minU a b).toNat ≤ b.toNat := by
  rw [min_toNat]
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

theorem max_bounds (a b : Word) :
    a.toNat ≤ (BinOp.eval .maxU a b).toNat ∧ b.toNat ≤ (BinOp.eval .maxU a b).toNat := by
  rw [max_toNat]
  exact ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩

/-- `eval`'s bin32 branch computes both operands from the incoming state, then
updates only the destination word register. The record equality also exposes
the unchanged PC successor, address registers, predicates, and memory. -/
theorem min_exec (guard : Guard) (s : State) (d : Nat) (a b : Operand32)
    (hg : guard.eval s = true) :
    eval none ⟨guard, .bin32 .minU d a b⟩ s =
      .next ⟨s.pc + 1, update s.regs d (BinOp.eval .minU (a.eval s) (b.eval s)),
        s.addrs, s.preds, s.memory⟩
        (occurrence s ⟨guard, .bin32 .minU d a b⟩ true) := by
  simp [eval, hg]

theorem max_exec (guard : Guard) (s : State) (d : Nat) (a b : Operand32)
    (hg : guard.eval s = true) :
    eval none ⟨guard, .bin32 .maxU d a b⟩ s =
      .next ⟨s.pc + 1, update s.regs d (BinOp.eval .maxU (a.eval s) (b.eval s)),
        s.addrs, s.preds, s.memory⟩
        (occurrence s ⟨guard, .bin32 .maxU d a b⟩ true) := by
  simp [eval, hg]

/-- The actual evaluated state leaves every non-destination word register at
its incoming value. `update_other` is the shared register-update fact used. -/
theorem min_exec_preserves_other (guard : Guard) (s : State) (d i : Nat)
    (a b : Operand32) (hg : guard.eval s = true) (hi : i ≠ d) :
    (match eval none ⟨guard, .bin32 .minU d a b⟩ s with
      | .next t _ => t.regs i | _ => s.regs i) = s.regs i := by
  rw [min_exec guard s d a b hg]
  exact update_other hi

theorem max_exec_preserves_other (guard : Guard) (s : State) (d i : Nat)
    (a b : Operand32) (hg : guard.eval s = true) (hi : i ≠ d) :
    (match eval none ⟨guard, .bin32 .maxU d a b⟩ s with
      | .next t _ => t.regs i | _ => s.regs i) = s.regs i := by
  rw [max_exec guard s d a b hg]
  exact update_other hi

theorem min_false (guard : Guard) (s : State) (d : Nat) (a b : Operand32)
    (hg : guard.eval s = false) :
    eval none ⟨guard, .bin32 .minU d a b⟩ s =
      .next ⟨s.pc + 1, s.regs, s.addrs, s.preds, s.memory⟩
        (occurrence s ⟨guard, .bin32 .minU d a b⟩ false) := by
  exact eval_skipped hg (by intro spelling; simp)

theorem max_false (guard : Guard) (s : State) (d : Nat) (a b : Operand32)
    (hg : guard.eval s = false) :
    eval none ⟨guard, .bin32 .maxU d a b⟩ s =
      .next ⟨s.pc + 1, s.regs, s.addrs, s.preds, s.memory⟩
        (occurrence s ⟨guard, .bin32 .maxU d a b⟩ false) := by
  exact eval_skipped hg (by intro spelling; simp)

-- The high bit is interpreted as an unsigned magnitude, and equality chooses
-- a value with the same bit pattern, including at ties.
example : BinOp.eval .minU (BitVec.ofNat 32 0x80000000) (BitVec.ofNat 32 7) =
    BitVec.ofNat 32 7 := by decide
example : BinOp.eval .maxU (BitVec.ofNat 32 0x80000000) (BitVec.ofNat 32 7) =
    BitVec.ofNat 32 0x80000000 := by decide
example : BinOp.eval .minU (BitVec.ofNat 32 9) (BitVec.ofNat 32 9) = BitVec.ofNat 32 9 := by decide
example : BinOp.eval .maxU (BitVec.ofNat 32 9) (BitVec.ofNat 32 9) = BitVec.ofNat 32 9 := by decide

example : decodeOp "min.u32" [.word (.reg 3), .word (.reg 1), .word (.imm 7)] =
    .ok (.bin32 .minU 3 (.reg 1) (.imm 7)) := by rfl
example : decodeOp "max.u32" [.word (.reg 3), .word (.imm 7), .word (.reg 1)] =
    .ok (.bin32 .maxU 3 (.imm 7) (.reg 1)) := by rfl
example : decodeOp "min.s32" [.word (.reg 0), .word (.imm 1), .word (.imm 2)] =
    .error (.unsupportedMnemonic "min.s32") := by rfl
example : decodeOp "max.relu.u32" [.word (.reg 0), .word (.imm 1), .word (.imm 2)] =
    .error (.unsupportedMnemonic "max.relu.u32") := by rfl
example : decodeOp "min.u32" [.word (.imm 0), .word (.imm 1), .word (.imm 2)] =
    .error (.invalidOperands "min.u32") := by rfl

def overlapState : State :=
  ⟨0, fun i => if i = 0 then BitVec.ofNat 32 8 else if i = 1 then BitVec.ofNat 32 5 else 0,
    fun _ => 0, fun i => i = 1, []⟩

-- Destination overlaps the left source: the right operand is read from the
-- incoming register file before the destination update.
example : (match eval none ⟨.always, .bin32 .minU 0 (.reg 0) (.reg 1)⟩ overlapState with
    | .next s _ => s.regs 0 | _ => 0) = BitVec.ofNat 32 5 := by
  simp [eval, overlapState, occurrence, Guard.eval, Operand32.eval, BinOp.eval, update]

-- Destination overlaps the right source: the left operand is likewise read
-- from the incoming register file.
example : (match eval none ⟨.always, .bin32 .maxU 1 (.reg 0) (.reg 1)⟩ overlapState with
    | .next s _ => s.regs 1 | _ => 0) = BitVec.ofNat 32 8 := by
  simp [eval, overlapState, occurrence, Guard.eval, Operand32.eval, BinOp.eval, update]

-- A false positive guard and a false negative guard both skip the instruction.
example : Guard.eval overlapState (.pred 0 true) = false := by rfl
example : Guard.eval overlapState (.pred 1 false) = false := by rfl
example : eval none ⟨.pred 0 true, .bin32 .minU 0 (.imm 1) (.imm 2)⟩ overlapState =
    .next ⟨1, overlapState.regs, overlapState.addrs, overlapState.preds, overlapState.memory⟩
      (occurrence overlapState ⟨.pred 0 true, .bin32 .minU 0 (.imm 1) (.imm 2)⟩ false) := by
  exact min_false _ _ _ _ _ rfl
example : eval none ⟨.pred 1 false, .bin32 .maxU 0 (.imm 1) (.imm 2)⟩ overlapState =
    .next ⟨1, overlapState.regs, overlapState.addrs, overlapState.preds, overlapState.memory⟩
      (occurrence overlapState ⟨.pred 1 false, .bin32 .maxU 0 (.imm 1) (.imm 2)⟩ false) := by
  exact max_false _ _ _ _ _ rfl

end Ptx.Scalar.IntegerMinMax
