import PoissonPTX.CellEntryRound

namespace PtxTorchLean.Poisson.PTX.CellEntry

/-- Arbitrary valid global inputs have a real finite concurrent gather prefix.
All lanes stop at the barrier, then all participants arrive and release it. -/
theorem prefix_exists (cfg : Concurrent.Config n) (ctx : Fin n → CellPrologue.Context) (start : State n)
    (pcs : ∀ u, (start.core.lanes u).pc=0)
    (reset : start.core.barrier=Ptx.Barrier.reset generation) (site : start.core.site=none)
    (initial : ∀ u, (start.core.lanes u).global=memory)
    (positive : 0<width) (fits : width*width<2^32)
    (valid : ∀ u, (ctx u).lane.toNat<width*width →
      CellGather.Valid (Local.beforeGather (ctx u) width (lane start u)) width cells source) :
    ∃ final events indices,
      Runs cfg ctx (program width cells source) start events indices final ∧
      (∀ u, (final.core.lanes u).pc=21) ∧
      final.core.barrier=Ptx.Barrier.reset (generation+1) ∧ final.core.site=none ∧
      Words memory events ∧ Indices memory indices := by
  let target := fun u => Before.finish (ctx u) width cells source (lane start u)
  let wordGood : Concurrent.Event n → Prop := fun e => match e with
    | .data _ a => a.data.store=false → a.space=.global → a.data.value=read64 memory a.data.address
    | .barrier _ => True
  let indexGood : Fin n × IndexSources.Access → Prop := fun (_,a) => a.value=read32 memory a.address
  obtain ⟨events,indices,first,words,ix⟩ := Serial.run_lanes (cfg:=cfg) (ctx:=ctx)
    (code:=program width cells source) start target wordGood indexGood (fun u state same barrierSame _ => by
      have localRun := Before.exists_trace (ctx u) (lane start u) (pcs u) positive fits (valid u)
      rw [← same] at localRun
      obtain ⟨es,is,run,reads,indexReads⟩ := record_local_run localRun
        (by rw [barrierSame,reset]; rfl)
      have global : (state.core.lanes u).global=memory := by
        exact (congrArg (fun s : CellPrologue.State => s.core.global) same).trans (initial u)
      refine ⟨es,is,?_,?_,?_⟩
      · simpa only [same] using run
      · intro e member
        cases e with
        | barrier => trivial
        | data owner a =>
          change a.data.store=false → a.space=.global → _
          rw [global] at reads
          exact reads owner a member
      · intro i member
        rw [global] at indexReads
        exact indexReads i.1 i.2 member)
  let middle := Serial.allLanes start target
  have atBarrier : ∀ u, (middle.core.lanes u).pc=20 := by
    intro u; exact Before.finish_pc (s:=lane start u) (pcs u)
  obtain ⟨barriers,last,onlyBarriers⟩ := barrier_round_exists (ctx:=ctx) cfg middle
    (program width cells source) 20 generation atBarrier reset site barrier_fetch
  refine ⟨afterRound middle generation,events++barriers,indices,?_,?_,rfl,rfl,?_,?_⟩
  · simpa using Serial.append first last
  · intro u; simp [afterRound,Concurrent.afterRound,advance,atBarrier]
  · intro owner a member read global
    rcases List.mem_append.mp member with earlier | later
    · exact words _ earlier read global
    · obtain ⟨b,wrong⟩ := onlyBarriers _ later; cases wrong
  · intro owner a member; exact ix (owner,a) member

end PtxTorchLean.Poisson.PTX.CellEntry
