import PoissonPTX.DotStageWave

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness

/-- Construct all nine native tree waves for arbitrary accumulator words. The
same physical program executes comparisons, branches, data and barriers. -/
theorem tree_candidate (start : NativeFlow.State 256) (ready : ReadyAt base 20 generation start)
    (aligned : base%8=0) (inputs : ∀ t, (start.core.lanes t).regs 8=input t.val) :
    ∃ final events indices, NativeFlow.Runs cfg ctx (program count left right output scratch) start events indices final ∧
      ReadyAt base 96 (generation+9) final ∧ ∀ e∈events, Expected input e := by
  obtain ⟨middle,firstEvents,firstIndices,first,middleReady,firstGood⟩ := initial_wave start ready aligned inputs
  have stages : ∀ k, k≤8 → ∃ final events indices,
      NativeFlow.Runs cfg ctx (program count left right output scratch) middle events indices final ∧
      ReadyAt base (24+9*k) (generation+1+k) final ∧ ∀ e∈events, Expected input e := by
    intro k bound
    induction k with
    | zero => exact ⟨middle,[],[],.nil,by simpa using middleReady,by simp⟩
    | succ k ih =>
      obtain ⟨before,earlier,earlierIndices,run,beforeReady,good⟩ := ih (by omega)
      obtain ⟨after,later,laterIndices,tail,afterReady,more⟩ := stage_wave before ⟨k,by omega⟩ beforeReady aligned input
      refine ⟨after,earlier++later,earlierIndices++laterIndices,NativeFlow.append run tail,?_,?_⟩
      · simpa only [Nat.add_assoc] using afterReady
      · intro e member
        rcases List.mem_append.mp member with earlier | later
        · exact good e earlier
        · exact more e later
  obtain ⟨final,later,laterIndices,rest,finalReady,lastGood⟩ := stages 8 (by omega)
  refine ⟨final,firstEvents++later,firstIndices++laterIndices,NativeFlow.append first rest,?_,?_⟩
  · simpa only [Nat.add_assoc] using finalReady
  · intro e member
    rcases List.mem_append.mp member with earlier | later
    · exact firstGood e earlier
    · exact lastGood e later

end PtxTorchLean.Poisson.PTX.Concurrent.Dot.Witness
