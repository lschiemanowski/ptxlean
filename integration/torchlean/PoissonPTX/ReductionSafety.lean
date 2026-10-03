import PoissonPTX.ReductionReads

namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control
variable {events : List (Event 256)} {thread : Fin 256} {access : Access}

theorem checked_memory_spaces : ∀ pc : Fin 68,
    (match program[pc.val]? with
    | some (.data (.load64 space _ _)) | some (.data (.store64 space _ _)) => decide (space=.shared)
    | _ => true)=true := by decide +kernel

theorem access_shared (run : Runs cfg program start events final)
    (member : Event.data thread access∈events) : access.space=.shared := by
  obtain ⟨before,earlier,selected,out,suffix,hp,hs,hm,ht,he⟩ := run_access_prefix run member
  obtain ⟨eq,op,next,fetch,hd⟩ := step_access_origin hs hm
  subst selected
  have check := checked_memory_spaces ⟨_,by
    have h := (List.getElem?_eq_some_iff.mp fetch).1; simpa only [length] using h⟩
  cases hd <;> simpa only [fetch,decide_eq_true_eq] using check

/-- Every actual access belongs to the aligned original 2048-byte shared region.
This result needs neither source admission nor a desired numerical answer. -/
theorem memory_safety {start : State 256} (run : Runs cfg program start events final)
    (aligned : Aligned start) (entry : ∀ t, (start.lanes t).pc=0)
    (baseReg : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (laneReg : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (baseAligned : base%8=0) (noWrap : base+2048≤2^64)
    (member : Event.data thread access∈events) :
    access.space=.shared ∧ Valid64 base 2048 access.data.address := by
  have shared := access_shared run member
  refine ⟨shared,?_⟩
  cases store : access.data.store with
  | true =>
    obtain ⟨w,hw⟩ := List.mem_iff_getElem?.mp member
    have address := lane_stores run aligned entry baseReg laneReg noWrap w thread access hw store shared
    rw [address]
    refine ⟨by omega,?_,by have := thread.isLt; omega,noWrap⟩
    simp [Nat.add_mod,baseAligned]
  | false =>
    obtain ⟨k,right,pc⟩ := read_coverage run member store
    obtain ⟨_,_,live,address⟩ := read_geometry run aligned entry baseReg laneReg noWrap k right member pc
    rw [address]
    have bounds := ranges k
    refine ⟨by omega,?_,?_,noWrap⟩
    · simp [Nat.add_mod,baseAligned]
    · cases right <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero] <;> omega

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control
