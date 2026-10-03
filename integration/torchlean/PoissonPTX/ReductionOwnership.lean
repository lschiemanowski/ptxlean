import PoissonPTX.ReductionControl
import PoissonPTX.ConcurrentAddressHold

/-! Actual shared-tree stores have their executing lane's address and belong
to a shrinking publication stage. No source/value constraints are needed. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control

/-- All instructions preserve the shared base and lane-number registers. -/
theorem checked_frames : ∀ pc : Fin 68,
    (match program[pc.val]? with
    | some (.data op) => AddressHold.keep 3 op && AddressHold.keep 14 op
    | _ => true)=true := by decide +kernel

theorem frames : Address.Keeps program 3 ∧ Address.Keeps program 14 := by
  have check (pc : Nat) (op : Op) (fetch : program[pc]?=some (.data op)) :
      SharedStore.keeps 3 op ∧ SharedStore.keeps 14 op := by
    have h := checked_frames ⟨pc, by
      have h := (List.getElem?_eq_some_iff.mp fetch).1; simpa only [length] using h⟩
    simpa only [fetch,Bool.and_eq_true,AddressHold.keep_correct] using h
  exact ⟨fun pc op fetch => (check pc op fetch).1,fun pc op fetch => (check pc op fetch).2⟩

theorem checked_entries : ∀ pc : Fin 68,
    (match program[pc.val]? with
    | some (.skip _ target) => decide (AddressHold.tag program target=.none)
    | _ => true)=true := by decide +kernel

theorem entries : AddressHold.Entries program := by
  intro pc count target fetch
  have h := checked_entries ⟨pc, by
    have h := (List.getElem?_eq_some_iff.mp fetch).1; simpa only [length] using h⟩
  simpa only [fetch,decide_eq_true_eq] using h

/-- Every shared store uses the prepared address, with zero optional offset. -/
theorem checked_addresses : ∀ pc : Fin 68,
    (match program[pc.val]? with
    | some (.data (.store64 .shared addr _)) =>
      decide (AddressHold.tag program pc.val=.addressed ∧ (addr=.reg 2 ∨ addr=.offset 2 0))
    | _ => true)=true := by decide +kernel

theorem lane_stores {start : State 256} (run : Runs cfg program start events final)
    (aligned : Aligned start) (entry : ∀ t, (start.lanes t).pc=0)
    (baseReg : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (laneReg : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (noWrap : base+2048≤2^64) : LaneStores events base := by
  intro index thread access found write shared
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ :=
    run_access_prefix run (List.mem_of_getElem? found)
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  have inv : AddressHold.Invariant program start := by
    intro t; rw [entry,AddressHold.tag_zero]; trivial
  have ready := AddressHold.runs_invariant hp aligned inv entries frames.1 frames.2 thread
  have baseEq : ((before.lanes thread).regs 3).toNat=base := by
    rw [Address.runs_keeps hp frames.1]; exact baseReg thread
  have laneEq : ((before.lanes thread).regs 14).toNat=thread.val := by
    rw [Address.runs_keeps hp frames.2]; exact laneReg thread
  have address := SharedStore.location_exact (before.lanes thread) 0
    (by rw [laneEq]; have := thread.isLt; omega)
    (by rw [baseEq,laneEq]; have := thread.isLt; change base+thread.val*8+0<2^64; omega)
  simp [SharedStore.location,baseEq,laneEq] at address
  cases hd with
  | store =>
    cases shared
    have h := checked_addresses ⟨_,by
      have h := (List.getElem?_eq_some_iff.mp fetch).1; simpa only [length] using h⟩
    simp only [fetch,decide_eq_true_eq] at h
    rw [h.1] at ready
    change (before.lanes thread).regs 2=(before.lanes thread).regs 3+wide (before.lanes thread) 14 at ready
    rcases h.2 with addr | addr <;> simp [addr,Operand.eval,ready,baseEq] <;> exact address
  | load => cases write

/-- Discharge the earlier source-selection theorem's store-coverage premise
for every actual finite execution of this shared-tree fragment. -/
theorem stage_stores {start : State 256} (run : Runs cfg program start events final)
    (aligned : Aligned start) (entry : ∀ t, (start.lanes t).pc=0)
    (baseReg : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (laneReg : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (noWrap : base+2048≤2^64) : StageStores events base site := by
  refine ⟨lane_stores run aligned entry baseReg laneReg noWrap,?_⟩
  intro index thread access found write shared
  exact store_coverage run aligned entry (List.mem_of_getElem? found) write shared

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control
