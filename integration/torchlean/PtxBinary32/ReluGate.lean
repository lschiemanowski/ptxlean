import PtxBinary32.Affine
import PtxBinary32.Relu

/-! An eight-instruction gate using existing scalar semantics. The first address
holds the decision word; the second the payload; the third the output. -/
namespace Ptx.Scalar.ReluGate
open Mixed

def load (i : Nat) : Scalar.Instr := .plain (.load i (.reg i))
def zeroTest : Scalar.Instr := .plain (.setp .eq 0 (.reg 0) (.imm 0))
def signTest : Scalar.Instr := .plain (.setp .ge 0 (.reg 0) (.imm 0x80000000))
def clear : Scalar.Instr := ⟨.pred 0 true, .mov32 1 (.imm 0)⟩
def store : Scalar.Instr := .plain (.store (.reg 2) (.reg 1))
def exit : Scalar.Instr := .plain .exit

def program : List Mixed.Instr :=
  [.scalar (load 0), .scalar (load 1), .scalar zeroTest, .scalar clear,
    .scalar signTest, .scalar clear, .scalar store, .scalar exit]

def Initial (s : State) : Prop :=
  s.pc = 0 ∧ ∀ i : Fin 3, ValidAddress s.memory (s.addrs i.val)

def input (s : State) (i : Nat) : Word := s.memory[(s.addrs i).toNat / 4]!
def afterLeft (s : State) : State :=
  {s with pc := 1, regs := update s.regs 0 (input s 0)}
def afterRight (s : State) : State :=
  {afterLeft s with pc := 2, regs := update (afterLeft s).regs 1 (input s 1)}
def afterZeroTest (s : State) : State :=
  {afterRight s with pc := 3, preds := update s.preds 0 (input s 0 == 0)}
def afterZero (s : State) : State :=
  {afterZeroTest s with pc := 4, regs := if input s 0 == 0 then update (afterRight s).regs 1 0 else (afterRight s).regs}
def afterSignTest (s : State) : State :=
  {afterZero s with pc := 5, preds := update s.preds 0 (decide ((input s 0).toNat ≥ 2147483648))}
def afterClear (s : State) : State :=
  {afterSignTest s with pc := 6, regs := if (input s 0).toNat ≥ 2147483648 then update (afterZero s).regs 1 0 else (afterZero s).regs}
def finish (s : State) : State :=
  {afterClear s with pc := 7, memory := s.memory.set ((s.addrs 2).toNat / 4) (Ptx.Binary32.Relu.gate (input s 0) (input s 1))}

private theorem step0 (h : Initial s) : Scalar.eval none (load 0) s =
    .next (afterLeft s) (Scalar.occurrence s (load 0) true (some ⟨.load, s.addrs 0, input s 0⟩)) := by
  have hi : addressIndex s.memory (s.addrs 0) = .ok ((s.addrs 0).toNat / 4) := addressIndex_ok_iff.mpr ⟨h.2 0, rfl⟩
  simp [load, Scalar.eval, Instr.plain, Guard.eval, Operand64.eval, hi, input,
    afterLeft, Scalar.occurrence, h.1]
private theorem step1 (h : Initial s) : Scalar.eval none (load 1) (afterLeft s) =
    .next (afterRight s) (Scalar.occurrence (afterLeft s) (load 1) true (some ⟨.load, s.addrs 1, input s 1⟩)) := by
  have hi : addressIndex s.memory (s.addrs 1) = .ok ((s.addrs 1).toNat / 4) := addressIndex_ok_iff.mpr ⟨h.2 1, rfl⟩
  simp [load, Scalar.eval, Instr.plain, Guard.eval, Operand64.eval, hi, input, afterLeft, afterRight]
private theorem step2 (s : State) : Scalar.eval none zeroTest (afterRight s) =
    .next (afterZeroTest s) (Scalar.occurrence (afterRight s) zeroTest true) := by
  simp [zeroTest, Scalar.eval, Instr.plain, Guard.eval, Operand32.eval,
    Compare.eval, afterZeroTest, afterRight, afterLeft]
private theorem step3 (s : State) : Scalar.eval none clear (afterZeroTest s) =
    .next (afterZero s) (Scalar.occurrence (afterZeroTest s) clear (input s 0 == 0)) := by
  by_cases h : input s 0 = 0#32 <;>
    simp [clear, Scalar.eval, Guard.eval, Operand32.eval, afterZero, afterZeroTest, h, beq_eq_false_iff_ne]
  all_goals rw [show (input s 0 == 0#32) = false from beq_eq_false_iff_ne.mpr h]
private theorem step4 (s : State) : Scalar.eval none signTest (afterZero s) =
    .next (afterSignTest s) (Scalar.occurrence (afterZero s) signTest true) := by
  by_cases h : input s 0 = 0#32 <;>
    simp [signTest, Scalar.eval, Instr.plain, Guard.eval, Operand32.eval,
      Compare.eval, afterSignTest, afterZero, afterZeroTest, afterRight, afterLeft, h, update, funext_iff]
  all_goals intro index; by_cases hi : index = 0 <;> simp [hi]
private theorem step5 (s : State) : Scalar.eval none clear (afterSignTest s) =
    .next (afterClear s) (Scalar.occurrence (afterSignTest s) clear
      (decide ((input s 0).toNat ≥ 2147483648))) := by
  by_cases h : (input s 0).toNat ≥ 2147483648 <;>
    simp [clear, Scalar.eval, Guard.eval, Operand32.eval, afterClear, afterSignTest, h]
private theorem step6 (h : Initial s) : Scalar.eval none store (afterClear s) =
    .next (finish s) (Scalar.occurrence (afterClear s) store true
      (some ⟨.store, s.addrs 2, Ptx.Binary32.Relu.gate (input s 0) (input s 1)⟩)) := by
  have hi : addressIndex s.memory (s.addrs 2) = .ok ((s.addrs 2).toNat / 4) := addressIndex_ok_iff.mpr ⟨h.2 2, rfl⟩
  by_cases hz : input s 0 = 0#32 <;> by_cases hn : (input s 0).toNat ≥ 2147483648
  all_goals
    have heq : (input s 0).toNat = 0 ↔ input s 0 = 0#32 := by exact BitVec.toNat_inj (x := input s 0) (y := 0#32)
    simp [store, Scalar.eval, Instr.plain, Guard.eval, Operand32.eval, Operand64.eval,
      afterClear, afterSignTest, afterZero, afterZeroTest, afterRight, afterLeft,
      finish, Ptx.Binary32.Relu.gate, Ptx.Binary32.Relu.positive, hi, hz, hn,
      show (0 < (input s 0).toNat) ↔ (input s 0 ≠ 0#32) by simpa only [Nat.pos_iff_ne_zero] using not_congr heq, not_le.mpr, not_lt.mpr]
  all_goals simp_all

theorem run_iff (s : State) (target : Target) (h : Initial s)
    (eligible : Mixed.Eligible target) (final : State) (status : Scalar.Stop) :
    (∃ events, Mixed.Run target program s final status events) ↔
      final = finish s ∧ status = .halted := by
  simp_rw [Mixed.Run.scalar_next_iff (program := program) eligible
    (by simp [program, h.1]) (step0 h)]
  simp_rw [Mixed.Run.scalar_next_iff (program := program) eligible
    (by simp [program, afterLeft]) (step1 h)]
  simp_rw [Mixed.Run.scalar_next_iff (program := program) eligible
    (by simp [program, afterRight]) (step2 s)]
  simp_rw [Mixed.Run.scalar_next_iff (program := program) eligible
    (by simp [program, afterZeroTest]) (step3 s)]
  simp_rw [Mixed.Run.scalar_next_iff (program := program) eligible
    (by simp [program, afterZero]) (step4 s)]
  simp_rw [Mixed.Run.scalar_next_iff (program := program) eligible
    (by simp [program, afterSignTest]) (step5 s)]
  simp_rw [Mixed.Run.scalar_next_iff (program := program) eligible
    (by simp [program, afterClear]) (step6 h)]
  simp_rw [Mixed.Run.scalar_halted_iff (program := program) eligible
    (by simp [program, finish]) (show Scalar.eval none exit (finish s) =
      .halted (finish s) (Scalar.occurrence (finish s) exit true) from rfl)]
  simp

theorem run_exists (s : State) (target : Target) (h : Initial s) (eligible : Mixed.Eligible target) :
    ∃ events, Mixed.Run target program s (finish s) .halted events :=
  (run_iff s target h eligible _ _).mpr ⟨rfl, rfl⟩

theorem run_memory (s : State) (target : Target) (h : Initial s) (eligible : Mixed.Eligible target)
    (run : Mixed.Run target program s final .halted events) :
    final.memory = s.memory.set ((s.addrs 2).toNat / 4) (Ptx.Binary32.Relu.gate (input s 0) (input s 1)) := by
  rw [((run_iff s target h eligible final .halted).mp ⟨events, run⟩).1]
  rfl

end Ptx.Scalar.ReluGate
