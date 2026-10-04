import PoissonPTX.DotTreeReads
import PoissonPTX.DotStoreProtection

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot
open Visibility.Repeated

theorem stride_double : ∀ phase : Fin 8,
    Reduction.active ⟨phase.val,by omega⟩=2*stride phase := by decide +kernel

/-- A tree read recovers the unique preceding publication of the selected lane.
Store occurrence, addresses, active ranges and causal order all come from the
same complete native run; only explicit byte-source admission is a premise. -/
theorem tree_read_source {cfg : Config 256} {ctx : Fin 256 → Kernel.Context} {r : Nat}
    (run : NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final)
    (reset : start.core.barrier=Ptx.Barrier.reset generation)
    (entry : ∀ thread, (start.core.lanes thread).pc=0)
    (laneMap : ∀ thread, (ctx thread).lane.toNat=thread.val)
    (noWrap : scratch.toNat+2048≤2^64)
    (compatible : Visibility.Compatible initial events source) (ordered : OrderedSources events source)
    (observed : events[r]?=some (.data reader access)) (phase : Fin 8) (neighbor : Bool)
    (site : access.data.pc=readPC phase neighbor) :
    ∃ (writer : Fin 256) (w : Nat) (wa : Access),
      writer.val=reader.val+readOffset phase neighbor ∧
      events[w]?=some (.data writer wa) ∧ wa.data.pc=storeSite ⟨phase.val,by omega⟩ ∧
      wa.data.store=true ∧ wa.space=.shared ∧ Visibility.Across events w r ∧
      access.data.value=wa.data.value ∧ ∀ k, source r k=.store w k := by
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
  have value : access.data.value=wa.data.value ∧ ∀ k, source r k=.store w k := by
    cases neighbor with
    | false =>
      have same : writer=reader := by apply Fin.ext; simp [writer,readOffset]
      subst writer
      exact NativeFlow.stage_own_read run suffix_forward stores store_sites suffix compatible ordered phase
        found observed write read sw shared address' previous
        (by rw [previous,site]; simp [storeSite,readPC])
        (by rw [site]; simp [storeSite,readPC]; omega)
    | true =>
      exact NativeFlow.stage_neighbor_read run suffix_forward stores store_sites suffix compatible ordered phase
        found observed write read sw shared address' previous
        (by change stride phase≤reader.val+readOffset phase true; simp [readOffset]) across
  exact ⟨writer,w,wa,rfl,found,previous,write,sw,across,value⟩

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
