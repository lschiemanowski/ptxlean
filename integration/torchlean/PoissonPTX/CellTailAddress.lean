import PoissonPTX.CellTailProgram

namespace PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address
open Ptx

/-- The widened byte offset computed from the low-word output index. -/
def scaled (s : PTX.State) (width : Nat) : Word := wide (CellFinal.indexed s width) 13

/-- No numerical value is assumed. These are scratch-address facts at actual
tail PCs and the read-after-write fact after an active lane's output store. -/
def Ready (cut width : Nat) (output : Word) (active : Prop) (s : PTX.State) : Prop :=
  (s.pc=cut+1 → s.regs 13=(CellFinal.index s width).setWidth 64) ∧
  (s.pc=cut+2 → s.regs 1=scaled s width) ∧
  (s.pc=cut+3 → s.regs 2=s.regs 0+scaled s width) ∧
  (s.pc=cut+4 → s.regs 2=CellFinal.location s width output) ∧
  (cut+5≤s.pc → active →
    read64 s.global (CellFinal.location s width output).toNat=s.regs 11)

theorem ready_before {active : Prop} (pc : s.pc≤cut) : Ready cut width output active s := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> intro h <;> omega

/-- The real fetched tail advances its address invariant one instruction at a
time. The valid store rule supplies the actual written bytes. -/
theorem tail_ready {active : Prop} (ready : Ready cut width output active s.core)
    (past : cut≤s.core.pc)
    (fetch : (CellFinal.tail width output)[s.core.pc-cut]?=some i)
    (eval : Kernel.Eval ctx i s next) :
    Ready cut width output active next.core := by
  have bound := (List.getElem?_eq_some_iff.mp fetch).1
  rw [tail_length] at bound
  have small : s.core.pc-cut<6 := bound
  interval_cases index : s.core.pc-cut <;>
    simp only [CellFinal.tail,storeCode,addressCode,List.map_cons,List.map_nil,
      List.cons_append,List.nil_append,List.getElem?_cons_zero,
      List.getElem?_cons_succ] at fetch
  all_goals cases fetch
  all_goals have pc : s.core.pc=cut+(s.core.pc-cut) := by omega
  all_goals simp only [index] at pc
  all_goals cases eval
  all_goals try {
    simp_all [Kernel.simple,Kernel.scalar,Kernel.halt,Kernel.advance,Ready,
      scaled,CellFinal.index,CellFinal.indexed,CellFinal.location,address,wide,
      assign,PTX.advance,Kernel.u32]
    done }
  all_goals rename_i he; cases he
  all_goals simp_all [Ready,scaled,CellFinal.index,CellFinal.indexed,CellFinal.location,
    address,wide,assign,PTX.advance,put,Operand.eval]

end PtxTorchLean.Poisson.PTX.Concurrent.CellConsumer.WithOutput.Address
