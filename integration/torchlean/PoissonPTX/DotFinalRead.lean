import PoissonPTX.DotTreeCorrect

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot
open Visibility.Repeated

theorem final_load_fetch : (program count left right output scratch)[98]?=
    some (.flow (.data (.data (.load64 .shared 8 (.reg 3))))) := by
  rw [show 98=96+2 by decide,tail_fetch]
  rfl

theorem final_read_layout
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (aligned : Aligned start.core) (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (member : Event.data reader access∈events) (site : access.data.pc=98) :
    access.data.store=false ∧ access.space=.shared ∧ access.data.address=scratch.toNat := by
  obtain ⟨before,earlier,earlierIndices,selected,out,prior,step,found⟩ := NativeFlow.access_prefix run member
  obtain ⟨same,i,next,index,fetch,effect⟩ := NativeFlow.step_access_origin step found
  subst selected
  have pc := (NativeFlow.eval_access_pc effect).1.symm.trans site
  change (before.core.lanes reader).pc=98 at pc
  have baseReg := (setup_registers prior aligned entry reader).1 (by change 0<(before.core.lanes reader).pc; omega)
  rw [pc,final_load_fetch] at fetch
  cases fetch
  cases effect with
  | data step => cases step with
    | data step => cases step with
      | load valid => exact ⟨rfl,rfl,congrArg BitVec.toNat baseReg⟩

/-- The last shared read observes lane zero's final tree publication. Other
lanes cannot overwrite its slot, and no later shared publication exists. -/
theorem final_read_source {cfg : Config 256} {ctx : Fin 256 → Kernel.Context} {r : Nat}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (noWrap : scratch.toNat+2048≤2^64)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (observed : events[r]?=some (.data reader access)) (site : access.data.pc=98) :
    ∃ w wa, events[w]?=some (.data 0 wa) ∧ wa.data.pc=storeSite 8 ∧
      wa.data.store=true ∧ wa.space=.shared ∧ Visibility.Across events w r ∧
      access.data.value=wa.data.value ∧ ∀ k, source r k=.store w k := by
  have aligned : Aligned start.core := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  obtain ⟨read,shared,address⟩ := final_read_layout run aligned entry (List.mem_of_getElem? observed) site
  obtain ⟨w,wa,found,previous,write,sw,across⟩ := publication_across (writer:=0) run reset entry laneMap
    8 (by decide +kernel) observed (by rw [site]; decide +kernel)
  have stores := shared_stage_stores run aligned entry laneMap noWrap
  have address' : access.data.address=scratch.toNat+(0 : Fin 256).val*8 := by simpa using address
  have allEarlier : ∀ (other : Nat) (a : Access), events[other]?=some (.data (0 : Fin 256) a) →
      a.data.store=true → a.space=.shared → a.data.pc≤wa.data.pc := by
    intro other a found write shared
    obtain ⟨phase,position,active⟩ := stores.2 other 0 a found write shared
    rw [position,previous]
    exact store_sites.monotone (by change phase.val≤8; have := phase.isLt; omega)
  have writers := NativeFlow.neighbor_writers_around (r:=r) run suffix_forward stores
    (fun phase => by simp [storeSite]; omega) found address' allEarlier
  have same : wa.data.address=access.data.address := (stores.1 w 0 wa found write sw).trans address'.symm
  have result := read_from_stage compatible ordered found observed write read sw shared same (.edge (.inr across)) writers
  exact ⟨w,wa,found,previous,write,sw,across,result⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
