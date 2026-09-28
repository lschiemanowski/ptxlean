import PtxBinary32.PointwiseReads

namespace Ptx.Scalar.Parallel.Pointwise
open Ptx.Binary32

/-- Arithmetic meaning of the live output register, indexed by fetched PC. -/
def RegisterValue (op : Op) (pc : Nat) (a b value : Word) : Prop :=
  match op with
  | .mul => Results .mul a b value
  | .copy => value=b
  | .difference => if pc=3 then Results .mul b 0xbf800000 value else Result .difference a b value
  | .gate => value=if pc<5 then b else if pc<7 then (if a=0 then 0 else b) else Relu.gate a b

structure Data (op : Op) (a b : Word) (s : Scalar.State) : Prop where
  left : 1≤s.pc → s.regs 4=a
  right : 2≤s.pc → s.regs 5=b
  result : 3≤s.pc → RegisterValue op s.pc a b (s.regs 6)
  zero : op=.gate → s.pc=4 → s.preds 1=(a==0)
  sign : op=.gate → s.pc=6 → s.preds 1=decide (a.toNat≥2147483648)

theorem gate_bits (a b : Word) :
    (if a.toNat≥2147483648 then 0 else if a=0 then 0 else b)=Relu.gate a b := by
  by_cases zero : a=0
  · subst a; simp [Relu.gate,Relu.positive]
  · have pos : 0<a.toNat := by
      have z : a.toNat≠0 := by intro h; exact zero (BitVec.eq_of_toNat_eq h)
      omega
    by_cases sign : a.toNat≥2147483648
    · simp [Relu.gate,Relu.positive,sign,not_lt.mpr sign]
    · simp [Relu.gate,Relu.positive,sign,not_le.mp sign,pos]
      intro h; exact False.elim (zero h)

theorem scalar_data (op : Op) (a b : Word) (state next : Scalar.State) (i : Scalar.Instr) (occ : Scalar.Occurrence)
    (data : Data op a b state)
    (fetch : (program op)[state.pc]?=some (.localStep i) ∨ ∃ space, (program op)[state.pc]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i state=.next next occ)
    (reads : ∀ e, occ.memory=some e → e.kind=.load → (occ.pc=0 → e.value=a) ∧ (occ.pc=1 → e.value=b)) :
    Data op a b next := by
  have bound : state.pc<(program op).length := by
    rcases fetch with h | ⟨_,h⟩ <;> exact (List.getElem?_eq_some_iff.mp h).choose
  generalize site : state.pc=pc at bound fetch
  cases op <;> simp [program,body] at bound
  all_goals interval_cases pc
  all_goals simp [program,body,localOp,clear] at fetch
  all_goals rcases fetch with rfl | ⟨_,rfl⟩
  all_goals obtain ⟨left,right,result,zero,sign⟩ := data
  all_goals simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand32.eval,Scalar.Operand64.eval] at evaluated
  all_goals cases enabled : state.preds 1 <;> simp only [enabled,Bool.false_eq_true,beq_self_eq_true,↓reduceIte] at evaluated
  all_goals repeat' (first | split at evaluated | contradiction)
  all_goals first | contradiction | skip
  all_goals obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj evaluated
  all_goals constructor
  all_goals simp only [Scalar.occurrence,Scalar.update,site,↓reduceIte,Nat.reduceAdd] at *
  all_goals intros
  all_goals first | omega | assumption | (apply left; omega) | (apply right; omega) | skip
  all_goals simp_all [RegisterValue,Scalar.Compare.eval]
  all_goals rw [← gate_bits]; simp_all

theorem fp_data (op : Op) (a b : Word) (state next : Scalar.State)
    (i : Scalar.Binary32.Instr) (occ : Scalar.Binary32.Occurrence)
    (data : Data op a b state) (fetch : (program op)[state.pc]?=some (.binary32 i))
    (ev : Scalar.Binary32.Eval i state next occ) : Data op a b next := by
  have bound : state.pc<(program op).length := (List.getElem?_eq_some_iff.mp fetch).choose
  generalize site : state.pc=pc at bound fetch
  cases op <;> simp [program,body] at bound
  all_goals interval_cases pc <;> simp [program,body,localOp,clear] at fetch
  all_goals subst i
  all_goals cases ev with
    | skipped no => cases no
    | @executed value enabled allowed =>
      simp only [Scalar.Operand32.eval] at allowed
      have left := data.left (by omega)
      have right := data.right (by omega)
      have old := data.result
      constructor <;> simp_all [Scalar.update,site,RegisterValue,Result]
      all_goals exact ⟨state.regs 6,old,allowed⟩

theorem scalar_store_data (op : Op) (a b : Word) (state next : Scalar.State)
    (i : Scalar.Instr) (space : Space) (occ : Scalar.Occurrence) (effect : MemoryEffect)
    (data : Data op a b state) (fetch : (program op)[state.pc]?=some (.memory space i))
    (evaluated : Scalar.eval candidate i state=.next next occ)
    (memory : occ.memory=some effect) (store : effect.kind=.store) : Result op a b effect.value := by
  have origin := Memory.Prior.eval_effect_origin candidate i state next occ effect evaluated memory
  have kind : Memory.Prior.memoryKind i.op=some .store := by simpa [store] using origin.2.2.2
  obtain ⟨_,pc,rfl⟩ := fetched_store op state.pc space i fetch kind
  have correct := data.result (by cases op <;> simp [storePC,body] at pc <;> omega)
  simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,↓reduceIte] at evaluated
  split at evaluated
  · contradiction
  · obtain ⟨_,rfl⟩ := Scalar.StepResult.next.inj evaluated
    simp only [Scalar.occurrence,Option.some.injEq] at memory
    subst effect
    cases op <;> simpa [RegisterValue,Result,pc,storePC,body,Scalar.Operand32.eval] using correct

end Ptx.Scalar.Parallel.Pointwise
