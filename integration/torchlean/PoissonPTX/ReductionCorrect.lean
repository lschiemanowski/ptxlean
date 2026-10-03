import PoissonPTX.ReductionNumerics

/-! Numerical correctness of actual shared-tree publications. Source rules
supply preceding store values; fetched arithmetic supplies each rounded sum. -/
namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric
open Visibility.Repeated
variable {events : List (Event 256)} {thread : Fin 256} {access : Access} {w : Nat}

theorem publication_limits : ∀ k : Fin 9, limit (site k)=active k := by decide +kernel

/-- Every actual publication is the prescribed rounded tree value. Inputs may
include exceptional binary64 values; only decoded values are equated. -/
theorem publication_value {start : State 256} (run : Runs cfg program start events final)
    (reset : start.barrier=Ptx.Barrier.reset generation) (entry : ∀ t, (start.lanes t).pc=0)
    (baseReg : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (laneReg : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (inputs : ∀ t, decode ((start.lanes t).regs 8)=input t.val)
    (noWrap : base+2048≤2^64)
    (compatible : Visibility.Compatible initialMemory events source) (ordered : OrderedSources events source)
    (phase : Fin 9) (observed : events[w]?=some (.data thread access))
    (pc : access.data.pc=site phase) : decode access.data.value=values input phase.val thread.val := by
  have aligned : Aligned start := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  have inv : Limits.Invariant limit start := by intro t; rw [entry]; exact t.isLt
  have all : ∀ (p : Nat) (bound : p<9) (w : Nat) (thread : Fin 256) (access : Access),
      events[w]?=some (.data thread access) → access.data.pc=site ⟨p,bound⟩ →
      decode access.data.value=values input p thread.val := by
    intro p
    induction p with
    | zero =>
      intro bound w thread access found atSite
      exact stored run aligned entry inputs (loadContract:=fun _ => none)
        (by intro t a h rd f hf; cases hf) ⟨0,bound⟩ initial_tag found atSite
    | succ p ih =>
      intro bound w thread access found atSite
      let k : Fin 8 := ⟨p,by omega⟩
      have reads : Values.Reads (loads input k) events := by
        intro reader ra member read f hf
        obtain ⟨r,hr⟩ := List.mem_iff_getElem?.mp member
        unfold loads at hf
        split at hf
        · rename_i atRead
          cases hf
          obtain ⟨v,owner,wa,ownerEq,hw,wp,ww,ws,value,bytes⟩ :=
            selected_read run reset entry baseReg laneReg noWrap compatible ordered k false hr atRead
          rw [value,ih (by omega) v owner wa hw wp]
          simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero] at ownerEq
          simp only [ownerEq,k]
        · split at hf
          · rename_i atRead
            cases hf
            obtain ⟨v,owner,wa,ownerEq,hw,wp,ww,ws,value,bytes⟩ :=
              selected_read run reset entry baseReg laneReg noWrap compatible ordered k true hr atRead
            rw [value,ih (by omega) v owner wa hw wp]
            simp only [↓reduceIte,ownerEq,k]
          · cases hf
      have sum := stored run aligned entry inputs reads (current k) (update_tag input k) found atSite
      have live := Limits.access_active run aligned inv boundaries (List.mem_of_getElem? found)
      rw [atSite,publication_limits] at live
      change thread.val<256 / 2^(p+1) at live
      simpa only [values,Binary64.round,live,↓reduceIte,k,current,active] using sum
  exact all phase.val phase.isLt w thread access observed pc

/-- A completed run actually contains lane zero's final store, whose decoded
word is the specified eight-round reduction of the original partial sums. -/
theorem completed_result {start : State 256} (run : Runs cfg program start events final)
    (reset : start.barrier=Ptx.Barrier.reset generation) (entry : ∀ t, (start.lanes t).pc=0)
    (baseReg : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (laneReg : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (inputs : ∀ t, decode ((start.lanes t).regs 8)=input t.val)
    (noWrap : base+2048≤2^64)
    (compatible : Visibility.Compatible initialMemory events source) (ordered : OrderedSources events source)
    (done : ∀ t, (final.lanes t).pc=program.length) :
    ∃ (w : Nat) (access : Access), events[w]?=some (.data 0 access) ∧
      access.data.pc=66 ∧ access.data.store=true ∧ access.space=.shared ∧
      access.data.address=base ∧ decode access.data.value=Binary64.reduce256 input := by
  have aligned : Aligned start := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  obtain ⟨access,member,pc,write,shared⟩ := crossed_store run aligned (store_fetch 8)
    (writer_stops 8 0 (by decide +kernel)) (by rw [entry]; decide +kernel)
    (by rw [done,length]; decide +kernel)
  obtain ⟨w,hw⟩ := List.mem_iff_getElem?.mp member
  have value := publication_value run reset entry baseReg laneReg inputs noWrap compatible ordered 8 hw pc
  have address := lane_stores run aligned entry baseReg laneReg noWrap w 0 access hw write shared
  change decode access.data.value=values input 8 0 at value
  rw [final_value] at value
  exact ⟨w,access,hw,pc,write,shared,by simpa using address,value⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Numeric
