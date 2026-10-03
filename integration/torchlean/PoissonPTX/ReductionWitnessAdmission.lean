import PoissonPTX.ReductionWitnessWords
import PoissonPTX.RepeatedSharedAdmission

namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256
open Visibility.Repeated
variable {events : List (Event 256)}

/-- Exact witness words agree with actual preceding publications. Control,
geometry and barrier history supply the producers and exclude intervening writes. -/
theorem admitted {start : State 256} (run : Runs cfg program start events final)
    (reset : start.barrier=Ptx.Barrier.reset generation) (entry : ∀ t, (start.lanes t).pc=0)
    (baseReg : ∀ t, ((start.lanes t).regs 3).toNat=base)
    (laneReg : ∀ t, ((start.lanes t).regs 14).toNat=t.val)
    (noWrap : base+2048≤2^64)
    (expected : ∀ e, e∈events → Expected input e) :
    ∃ source, Visibility.Compatible initialMemory events source ∧ OrderedSources events source := by
  apply construct_sources events
  intro r reader ra hr read
  have aligned : Aligned start := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  obtain ⟨k,right,pc⟩ := read_coverage run (List.mem_of_getElem? hr) read
  obtain ⟨read,shared,live,address⟩ := read_geometry run aligned entry baseReg laneReg noWrap k right
    (List.mem_of_getElem? hr) pc
  have bounds := ranges k
  let owner : Fin 256 := ⟨reader.val+(if right then active (current k) else 0),by split <;> omega⟩
  have ownerLive : owner.val<active (previous k) := by dsimp [owner]; split <;> omega
  have later : site (previous k)+1<ra.data.pc := by rw [pc]; dsimp [site,previous,readPC]; split <;> omega
  obtain ⟨w,wa,hw,position,write,space,across⟩ := published run reset entry (previous k) owner ownerLive hr later
  have stores := stage_stores run aligned entry baseReg laneReg noWrap
  have word := (expected _ (List.mem_of_getElem? hw)).1 (previous k) position
  have loaded := (expected _ (List.mem_of_getElem? hr)).2 k right pc
  have before : w<r := before_lt (.edge (.inr across))
  refine ⟨w,owner,wa,hw,write,space,shared,(stores.1 w owner wa hw write space).trans address.symm,
    ?_,before,?_⟩
  · rw [word,loaded]; rfl
  · cases right with
    | false =>
      have eq : owner=reader := by apply Fin.ext; simp [owner]
      subst owner
      apply own_writers_around run forward stores.1 hw hr (by simpa using address)
      intro other a found store shared
      exact own_gap stores sites k position (by rw [pc]; dsimp [readPC,site]; omega) found store shared
    | true =>
      apply neighbor_writers_around run forward stores.1 hw address
      intro other a found store shared
      exact neighbor_last stores sites k position
        (by change active (current k)≤reader.val+active (current k); omega) found store shared

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Control.Witness256
