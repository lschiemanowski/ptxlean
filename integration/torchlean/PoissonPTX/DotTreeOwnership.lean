import PoissonPTX.DotTreeAddress
import PoissonPTX.DotStoreSyntax
import PoissonPTX.NativeFlowStageSources

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

def storeSite (phase : Fin 9) : Nat := 22+9*phase.val

theorem store_sites : StrictMono storeSite := by
  intro a b h
  change 22+9*a.val<22+9*b.val
  change a.val<b.val at h
  omega

theorem checked_shared_stores : ∀ slot : Fin 76,
    (match Reduction.Native.code[slot.val]? with
    | some (.data (.store64 .shared addr _)) => decide (∃ phase : Fin 9,
        20+slot.val=storeSite phase ∧ treeLimit (20+slot.val)=Reduction.active phase ∧
        treeAddressTag (20+slot.val)=.addressed ∧ (addr=.reg 2 ∨ addr=.offset 2 0))
    | _ => true)=true := by decide +kernel

/-- Every shared store in the complete entry is one of the nine lane-owned
publications. This classification is a check of fetched syntax. -/
theorem shared_store_site
    (fetch : (program count left right output scratch)[pc]?=
      some (.flow (.data (.data (.store64 .shared addr src))))) :
    ∃ phase : Fin 9, pc=storeSite phase ∧ treeLimit pc=Reduction.active phase ∧
      treeAddressTag pc=.addressed ∧ (addr=.reg 2 ∨ addr=.offset 2 0) := by
  by_cases before : pc<20
  · rw [input_fetch before] at fetch
    obtain ⟨i,found,equal⟩ := Option.map_eq_some_iff.mp fetch
    cases equal
    have safe := input_safe (List.mem_of_getElem? found)
    cases safe
  · by_cases inside : pc<96
    · have position : pc=20+(pc-20) := by omega
      rw [position,tree_fetch (by omega)] at fetch
      obtain ⟨native,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      have checked := checked_shared_stores ⟨pc-20,by omega⟩
      rw [found] at checked
      cases native <;> cases equal
      simpa only [← position,decide_eq_true_eq] using checked
    · have position : pc=96+(pc-96) := by omega
      rw [position,tail_fetch] at fetch
      obtain ⟨i,found,equal⟩ := Option.map_eq_some_iff.mp fetch
      cases equal
      have member := List.mem_of_getElem? found
      simp [tail] at member

/-- Actual address instructions and branch predicates jointly establish store
ownership and the shrinking active range. No shared value is assumed here. -/
theorem shared_store_ownership {cfg : Config 256} {ctx : Fin 256 → Kernel.Context}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (noWrap : scratch.toNat+2048≤2^64)
    (member : Event.data owner access∈events) (write : access.data.store=true) (shared : access.space=.shared) :
    access.data.address=scratch.toNat+owner.val*8 ∧
      ∃ phase : Fin 9, access.data.pc=storeSite phase ∧ owner.val<Reduction.active phase := by
  obtain ⟨before,earlier,earlierIndices,selected,out,earlierRun,step,found⟩ := NativeFlow.access_prefix run member
  obtain ⟨same,i,next,index,fetch,effect⟩ := NativeFlow.step_access_origin step found
  subst selected
  obtain ⟨space,addr,src,op,shape⟩ := Flow.Observed.store_shape effect write
  subst i
  have spaceEq : space=.shared := by simpa only [shape] using shared
  subst space
  obtain ⟨phase,pc,limit,tag,addressForm⟩ := shared_store_site fetch
  have active := (tree_control earlierRun aligned entry laneMap owner).1
  have prepared := tree_addresses earlierRun aligned entry owner
  have regs := setup_registers earlierRun aligned entry owner
  have after : 20≤(before.core.lanes owner).pc := by rw [pc]; simp [storeSite]; omega
  have baseReg := regs.1 (by change 0<(before.core.lanes owner).pc; omega)
  have laneReg := regs.2 (by change 2<(before.core.lanes owner).pc; omega)
  have laneValue : ((before.core.lanes owner).regs 14).toNat=owner.val := by
    change ((NativeFlow.lane before owner).core.regs 14).toNat = owner.val
    rw [laneReg]
    simp [BitVec.toNat_setWidth,laneMap,Nat.mod_eq_of_lt (show owner.val<18446744073709551616 by have := owner.isLt; omega)]
  change Address.Ready (treeAddressTag (before.core.lanes owner).pc) (before.core.lanes owner) at prepared
  rw [tag] at prepared
  change (before.core.lanes owner).regs 2=(before.core.lanes owner).regs 3+wide (before.core.lanes owner) 14 at prepared
  have location := SharedStore.location_exact (before.core.lanes owner) 0
    (by rw [laneValue]; have := owner.isLt; omega)
    (by rw [laneValue]; change ((before.core.lanes owner).regs 3).toNat+owner.val*8+0<2^64
        change ((NativeFlow.lane before owner).core.regs 3).toNat+owner.val*8+0<2^64
        rw [baseReg]; have := owner.isLt; omega)
  simp only [SharedStore.location,laneValue] at location
  have baseEq : (before.core.lanes owner).regs 3=scratch := baseReg
  rw [baseEq] at location
  refine ⟨?_,phase,?_,?_⟩
  · rcases addressForm with rfl|rfl <;> simp only [shape,Operand.eval,NativeFlow.lane]
    all_goals simpa [prepared,baseEq] using location
  · simpa only [shape,NativeFlow.lane] using pc
  · change owner.val<treeLimit (before.core.lanes owner).pc at active
    simpa only [limit] using active

theorem shared_stage_stores {cfg : Config 256} {ctx : Fin 256 → Kernel.Context}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (noWrap : scratch.toNat+2048≤2^64) : Reduction.StageStores events scratch.toNat storeSite := by
  constructor
  · intro index owner access found write shared
    exact (shared_store_ownership run aligned entry laneMap noWrap (List.mem_of_getElem? found) write shared).1
  · intro index owner access found write shared
    exact (shared_store_ownership run aligned entry laneMap noWrap (List.mem_of_getElem? found) write shared).2

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
