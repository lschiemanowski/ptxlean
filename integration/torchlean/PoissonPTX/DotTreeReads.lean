import PoissonPTX.DotTreeOwnership

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

def stride (phase : Fin 8) : Nat := Reduction.active ⟨phase.val+1,by omega⟩
def readPC (phase : Fin 8) (neighbor : Bool) : Nat := 28+9*phase.val+if neighbor then 1 else 0
def readOffset (phase : Fin 8) (neighbor : Bool) : Nat := if neighbor then stride phase else 0
def readOperand (phase : Fin 8) (neighbor : Bool) : Operand :=
  if neighbor then .offset 2 (BitVec.ofNat 64 (8*stride phase)) else .reg 2

theorem checked_read_fetch : ∀ (phase : Fin 8) (neighbor : Bool),
    Reduction.Native.code[readPC phase neighbor-20]?=
      some (.data (.load64 .shared (if neighbor then 5 else 4) (readOperand phase neighbor))) := by decide +kernel

theorem read_fetch (phase : Fin 8) (neighbor : Bool) :
    (program count left right output scratch)[readPC phase neighbor]?=
      some (.flow (.data (.data (.load64 .shared (if neighbor then 5 else 4) (readOperand phase neighbor))))) := by
  have bounds : 20≤readPC phase neighbor ∧ readPC phase neighbor<96 := by
    unfold readPC; have := phase.isLt; cases neighbor <;> simp_all <;> omega
  have position : readPC phase neighbor=20+(readPC phase neighbor-20) := by omega
  rw [position,tree_fetch (by omega)]
  rw [checked_read_fetch]
  rfl

theorem checked_read_layout : ∀ (phase : Fin 8) (neighbor : Bool),
    treeLimit (readPC phase neighbor)=stride phase ∧
    treeAddressTag (readPC phase neighbor)=.addressed ∧
    2*stride phase≤256 := by decide +kernel

/-- The actual shared read addresses its own or its neighbor's slot, and the
actual branch bounds both slots inside the 256-word scratch allocation. -/
theorem tree_read_layout {cfg : Config 256} {ctx : Fin 256 → Kernel.Context}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (noWrap : scratch.toNat+2048≤2^64)
    (member : Event.data owner access∈events) (phase : Fin 8) (neighbor : Bool)
    (site : access.data.pc=readPC phase neighbor) :
    access.data.store=false ∧ access.space=.shared ∧ owner.val<stride phase ∧
      owner.val+readOffset phase neighbor<256 ∧
      access.data.address=scratch.toNat+(owner.val+readOffset phase neighbor)*8 := by
  obtain ⟨before,earlier,earlierIndices,selected,out,earlierRun,step,found⟩ := NativeFlow.access_prefix run member
  obtain ⟨same,i,next,index,fetch,effect⟩ := NativeFlow.step_access_origin step found
  subst selected
  have pc := (NativeFlow.eval_access_pc effect).1.symm.trans site
  change (before.core.lanes owner).pc=readPC phase neighbor at pc
  rw [pc,read_fetch] at fetch
  cases fetch
  have checked := checked_read_layout phase neighbor
  have active := (tree_control earlierRun aligned entry laneMap owner).1
  change owner.val<treeLimit (before.core.lanes owner).pc at active
  rw [pc,checked.1] at active
  have after : 20≤(before.core.lanes owner).pc := by
    rw [pc]; unfold readPC; cases neighbor <;> simp <;> omega
  have regs := setup_registers earlierRun aligned entry owner
  have baseReg : (before.core.lanes owner).regs 3=scratch := regs.1 (by change 0<(before.core.lanes owner).pc; omega)
  have laneReg : (before.core.lanes owner).regs 14=(ctx owner).lane.setWidth 64 := regs.2 (by change 2<(before.core.lanes owner).pc; omega)
  have laneValue : ((before.core.lanes owner).regs 14).toNat=owner.val := by
    simp [laneReg,BitVec.toNat_setWidth,laneMap,Nat.mod_eq_of_lt (show owner.val<18446744073709551616 by have := owner.isLt; omega)]
  have prepared := tree_addresses earlierRun aligned entry owner
  change Address.Ready (treeAddressTag (before.core.lanes owner).pc) (before.core.lanes owner) at prepared
  rw [pc,checked.2.1] at prepared
  change (before.core.lanes owner).regs 2=(before.core.lanes owner).regs 3+wide (before.core.lanes owner) 14 at prepared
  have within : owner.val+readOffset phase neighbor<256 := by
    unfold readOffset; cases neighbor <;> simp_all
    omega
  let offset := BitVec.ofNat 64 (readOffset phase neighbor*8)
  have offsetNat : offset.toNat=readOffset phase neighbor*8 := by
    apply Nat.mod_eq_of_lt
    omega
  have location := SharedStore.location_exact (before.core.lanes owner) offset
    (by rw [laneValue]; have := owner.isLt; omega)
    (by rw [baseReg,laneValue,offsetNat]; omega)
  simp only [SharedStore.location,baseReg,laneValue,offsetNat] at location
  have address : ((readOperand phase neighbor).eval (before.core.lanes owner)).toNat=
      scratch.toNat+(owner.val+readOffset phase neighbor)*8 := by
    have rhs : scratch.toNat+owner.val*8+readOffset phase neighbor*8=
        scratch.toNat+(owner.val+readOffset phase neighbor)*8 := by omega
    rw [← rhs]
    convert location using 1
    cases neighbor <;> simp [readOperand,readOffset,offset,Operand.eval,prepared,baseReg,Nat.mul_comm]
  cases effect with
  | data step =>
    cases step with
    | data step =>
      cases step with
      | load valid => exact ⟨rfl,rfl,active,within,address⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
