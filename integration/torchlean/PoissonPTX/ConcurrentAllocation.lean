import PoissonPTX.ByteHistoryStep

namespace PtxTorchLean.Poisson.PTX.Concurrent

/-- Instruction execution changes bytes and registers but not the physical
allocation bounds supplied at launch. Barrier release only advances PCs. -/
theorem step_allocation {start : State n} (step : Step cfg code selected start out) (thread : Fin n) :
    (out.state.lanes thread).start=(start.lanes thread).start ∧
    (out.state.lanes thread).bytes=(start.lanes thread).bytes := by
  obtain ⟨_,i,_,actual⟩ := step
  cases actual with
  | data h =>
    by_cases same : thread=selected
    · subst thread
      simpa only [setLane,Function.update_self] using ByteHistory.data_allocation h
    · simp [setLane,Function.update_of_ne same]
  | skip =>
    by_cases same : thread=selected
    · subst thread; simp only [setLane,Function.update_self]; exact ⟨rfl,rfl⟩
    · simp [setLane,Function.update_of_ne same]
  | sync => simp only [synchronize]; split <;> exact ⟨rfl,rfl⟩

theorem runs_allocation {start : State n} (run : Runs cfg code start events final) (thread : Fin n) :
    (final.lanes thread).start=(start.lanes thread).start ∧
    (final.lanes thread).bytes=(start.lanes thread).bytes := by
  induction run with
  | nil => exact ⟨rfl,rfl⟩
  | cons step _ ih =>
    have frame := step_allocation step thread
    exact ⟨ih.1.trans frame.1,ih.2.trans frame.2⟩

end PtxTorchLean.Poisson.PTX.Concurrent
