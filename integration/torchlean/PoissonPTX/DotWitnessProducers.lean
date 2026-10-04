import PoissonPTX.DotFinalRead
import PoissonPTX.DotWitnessWords
import PoissonPTX.GlobalSharedAdmission

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
open Reduction.Control.Witness256 Visibility.Repeated

/-- Recover an actual preceding store for a candidate tree read. The candidate
words are established by construction; barrier and competing-writer evidence
is recovered independently from the complete native run. -/
theorem tree_producer {cfg : Config 256} {ctx : Fin 256 → Kernel.Context} {r : Nat}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (noWrap : scratch.toNat+2048≤2^64)
    (stored : ∀ (w : Nat) (owner : Fin 256) (wa : Access), events[w]?=some (.data owner wa) →
      ∀ phase : Fin 9, wa.data.pc=storeSite phase → wa.data.value=words input phase.val owner.val)
    (observed : events[r]?=some (.data reader access)) (phase : Fin 8) (neighbor : Bool)
    (site : access.data.pc=readPC phase neighbor)
    (value : access.data.value=words input phase.val (reader.val+readOffset phase neighbor)) :
    ∃ w, Producer events r access w := by
  have aligned : Aligned start.core := by intro t h; simp [reset,Ptx.Barrier.reset] at h
  obtain ⟨read,shared,active,within,address⟩ := tree_read_layout run aligned entry laneMap noWrap
    (List.mem_of_getElem? observed) phase neighbor site
  let writer : Fin 256 := ⟨reader.val+readOffset phase neighbor,within⟩
  have writerActive : writer.val<Reduction.active ⟨phase.val,by omega⟩ := by
    rw [stride_double]
    change reader.val+readOffset phase neighbor<2*stride phase
    cases neighbor <;> simp only [readOffset,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] <;> omega
  have later : barrierSite ⟨phase.val,by omega⟩<access.data.pc := by
    rw [site]; unfold barrierSite readPC; cases neighbor <;> simp
  obtain ⟨w,wa,found,previous,write,sw,across⟩ := publication_across run reset entry laneMap
    ⟨phase.val,by omega⟩ writerActive observed later
  have stores := shared_stage_stores run aligned entry laneMap noWrap
  have suffix : ∀ stage, 20≤storeSite stage := by intro stage; simp [storeSite]; omega
  have address' : access.data.address=scratch.toNat+writer.val*8 := address
  refine ⟨w,writer,wa,found,write,sw,shared,(stores.1 w writer wa found write sw).trans address'.symm,
    ?_,before_lt (.edge (.inr across)),?_⟩
  · rw [stored w writer wa found ⟨phase.val,by omega⟩ previous,value]
  · cases neighbor with
    | false =>
      have same : writer=reader := by apply Fin.ext; simp [writer,readOffset]
      subst writer
      apply NativeFlow.own_writers_around run suffix_forward stores suffix found observed address'
      · intro other a hw ww ws
        exact Reduction.own_gap stores store_sites phase previous
          (by rw [site]; simp [storeSite,readPC]; omega) hw ww ws
      · rw [site]; simp [readPC]; omega
    | true =>
      apply NativeFlow.neighbor_writers_around run suffix_forward stores suffix found address'
      intro other a hw ww ws
      exact Reduction.neighbor_last stores store_sites phase previous
        (by change stride phase≤reader.val+readOffset phase true; simp [readOffset]) hw ww ws

theorem final_producer {cfg : Config 256} {ctx : Fin 256 → Kernel.Context} {r : Nat}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (noWrap : scratch.toNat+2048≤2^64)
    (stored : ∀ (w : Nat) (owner : Fin 256) (wa : Access), events[w]?=some (.data owner wa) →
      ∀ phase : Fin 9, wa.data.pc=storeSite phase → wa.data.value=words input phase.val owner.val)
    (observed : events[r]?=some (.data reader access)) (site : access.data.pc=98)
    (value : access.data.value=words input 8 0) : ∃ w, Producer events r access w := by
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
  refine ⟨w,0,wa,found,write,sw,shared,(stores.1 w 0 wa found write sw).trans address'.symm,?_,
    before_lt (.edge (.inr across)),writers⟩
  rw [stored w 0 wa found 8 previous,value]
  rfl

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
