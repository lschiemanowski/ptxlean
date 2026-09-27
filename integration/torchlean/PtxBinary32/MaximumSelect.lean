import PtxBinary32.Maximum
import PtxBinary32.ParallelSegment

/-! An exact two-word maximum selector built from existing integer instructions.
The finite-real interpretation is separate from the total bit computation. -/
namespace Ptx.Scalar.MaximumSelect
open Parallel

def code : List Parallel.Instr := [
  .localStep (.plain (.setp .ge 1 (.reg 4) (.imm 0x80000000))),
  .localStep (.plain (.bin32 .xor 8 (.reg 4) (.imm 0x80000000))),
  .localStep ⟨.pred 1 true,.bin32 .xor 8 (.reg 4) (.imm 0xffffffff)⟩,
  .localStep (.plain (.setp .ge 1 (.reg 5) (.imm 0x80000000))),
  .localStep (.plain (.bin32 .xor 9 (.reg 5) (.imm 0x80000000))),
  .localStep ⟨.pred 1 true,.bin32 .xor 9 (.reg 5) (.imm 0xffffffff)⟩,
  .localStep (.plain (.setp .lt 1 (.reg 8) (.reg 9))),
  .localStep (.plain (.mov32 6 (.reg 4))),
  .localStep ⟨.pred 1 true,.mov32 6 (.reg 5)⟩]

@[simp] theorem code_length : code.length = 9 := rfl

def finish (s : Scalar.State) : Scalar.State :=
  {s with
    pc := s.pc + 9
    regs := Scalar.update (Scalar.update (Scalar.update s.regs 8
      (Ptx.Binary32.Maximum.key (s.regs 4))) 9
      (Ptx.Binary32.Maximum.key (s.regs 5))) 6
      (Ptx.Binary32.Maximum.choose (s.regs 4) (s.regs 5))
    preds := Scalar.update s.preds 1
      (decide ((Ptx.Binary32.Maximum.key (s.regs 4)).toNat <
        (Ptx.Binary32.Maximum.key (s.regs 5)).toNat))
    memory := []}

/-- Only the selected lane changes; shared/global storage and barriers do not. -/
def install (s : Parallel.State n) (t : Fin n) : Parallel.State n :=
  Parallel.setLane s t {s.lanes t with scalar := finish (s.lanes t).scalar}

private theorem shadow (f : Nat → α) (i : Nat) (a b : α) :
    Scalar.update (Scalar.update f i a) i b = Scalar.update f i b := by
  funext j
  by_cases h : j=i <;> simp [Scalar.update,h]

def keyCode (source destination : Nat) : List Parallel.Instr := [
  .localStep (.plain (.setp .ge 1 (.reg source) (.imm 0x80000000))),
  .localStep (.plain (.bin32 .xor destination (.reg source) (.imm 0x80000000))),
  .localStep ⟨.pred 1 true,.bin32 .xor destination (.reg source) (.imm 0xffffffff)⟩]

def keyInstall (s : Parallel.State n) (t : Fin n) (source destination : Nat) : Parallel.State n :=
  let old := (s.lanes t).scalar
  setLane s t {s.lanes t with scalar := {old with
    pc := old.pc+3
    regs := Scalar.update old.regs destination (Ptx.Binary32.Maximum.key (old.regs source))
    preds := Scalar.update old.preds 1 (decide ((old.regs source).toNat ≥ 2147483648))
    memory := []}}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem key_execution (cfg : Parallel.Config n) (t : Fin n) (s : Parallel.State n)
    (source destination : Nat) (different : source ≠ destination) :
    SegmentRegular cfg t (keyCode source destination) s ∧
    (segmentReference cfg t (keyCode source destination) s).1 = keyInstall s t source destination := by
  by_cases ha : ((s.lanes t).scalar.regs source).toNat ≥ 2147483648
  all_goals
    simp [SegmentRegular, segmentReference, Reference.dispatch, keyCode,
      scalarStep, Scalar.eval, arena, setLane, Function.update,
      Scalar.Instr.plain, Scalar.Guard.eval, Scalar.Operand32.eval,
      Scalar.Compare.eval, Scalar.BinOp.eval, Scalar.update,
      keyInstall, Ptx.Binary32.Maximum.key, ha, different, shadow, Nat.add_assoc]

def selectCode : List Parallel.Instr := [
  .localStep (.plain (.setp .lt 1 (.reg 8) (.reg 9))),
  .localStep (.plain (.mov32 6 (.reg 4))),
  .localStep ⟨.pred 1 true,.mov32 6 (.reg 5)⟩]

def selectInstall (s : Parallel.State n) (t : Fin n) : Parallel.State n :=
  let old := (s.lanes t).scalar
  setLane s t {s.lanes t with scalar := {old with
    pc := old.pc+3
    regs := Scalar.update old.regs 6 (if (old.regs 8).toNat < (old.regs 9).toNat then old.regs 5 else old.regs 4)
    preds := Scalar.update old.preds 1 (decide ((old.regs 8).toNat < (old.regs 9).toNat))
    memory := []}}

theorem select_execution (cfg : Parallel.Config n) (t : Fin n) (s : Parallel.State n) :
    SegmentRegular cfg t selectCode s ∧
    (segmentReference cfg t selectCode s).1 = selectInstall s t := by
  by_cases h : ((s.lanes t).scalar.regs 8).toNat < ((s.lanes t).scalar.regs 9).toNat
  all_goals
    simp [SegmentRegular, segmentReference, Reference.dispatch, selectCode,
      scalarStep, Scalar.eval, arena, setLane, Function.update,
      Scalar.Instr.plain, Scalar.Guard.eval, Scalar.Operand32.eval,
      Scalar.Compare.eval, Scalar.update, selectInstall, h, shadow, Nat.add_assoc]

private theorem code_split : code = keyCode 4 8 ++ keyCode 5 9 ++ selectCode := rfl

theorem reference (cfg : Parallel.Config n) (t : Fin n) (s : Parallel.State n) :
    (Parallel.segmentReference cfg t code s).1 = install s t := by
  rw [code_split,segmentReference_append,segmentReference_append]
  simp only [key_execution cfg t s 4 8 (by decide) |>.2]
  rw [(key_execution cfg t _ 5 9 (by decide)).2]
  rw [(select_execution cfg t _).2]
  simp [keyInstall,selectInstall,install,finish,setLane,Function.update,
    Scalar.update,Ptx.Binary32.Maximum.choose,shadow,Nat.add_assoc]

theorem regular (cfg : Parallel.Config n) (t : Fin n) (s : Parallel.State n) :
    SegmentRegular cfg t code s := by
  rw [code_split,segmentRegular_append,segmentRegular_append]
  exact ⟨⟨(key_execution cfg t s 4 8 (by decide)).1,
    (key_execution cfg t _ 5 9 (by decide)).1⟩,(select_execution cfg t _).1⟩

end Ptx.Scalar.MaximumSelect
