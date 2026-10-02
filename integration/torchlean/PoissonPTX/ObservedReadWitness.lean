import PoissonPTX.ObservedExists

namespace PtxTorchLean.Poisson.PTX.Flow.Observed

/-- The recording construction retains exact load bits from the ordinary
execution's current memory. This is stronger than bare record existence. -/
theorem data_read_witness (step : Indexed.Eval op s t) :
    ∃ access index, Indexed.Candidate.Data op s t access index ∧
      (∀ a, access=some a → a.data.store=false → a.data.value=read64 (s.memory a.space) a.data.address) ∧
      (∀ a, index=some a → a.value=read32 s.global a.address) := by
  cases step with
  | data one =>
    cases one with
    | load64 valid => exact ⟨_,_,.data (.load valid),by intro a eq _; cases eq; rfl,by simp⟩
    | store64 valid => exact ⟨_,_,.data (.store valid),by intro a eq store; cases eq; simp at store,by simp⟩
    | _ => exact ⟨none,none,.data (.ordinary rfl (by constructor <;> assumption)),by simp,by simp⟩
  | mad32 => exact ⟨none,none,.mad32,by simp,by simp⟩
  | wide4 => exact ⟨none,none,.wide4,by simp,by simp⟩
  | load32 valid => exact ⟨none,_,.load32 valid,by simp,by intro a eq; cases eq; rfl⟩

theorem step_read_witness (step : Flow.Step ctx program s t) :
    ∃ access index, Step ctx program s t access index ∧
      (∀ a, access=some a → a.data.store=false → a.data.value=read64 (s.core.memory a.space) a.data.address) ∧
      (∀ a, index=some a → a.value=read32 s.core.global a.address) := by
  obtain ⟨running,_,fetch,execution⟩ := step
  cases execution with
  | data one =>
    obtain ⟨access,index,recorded,words,indices⟩ := data_read_witness one
    exact ⟨access,index,⟨running,_,fetch,.data recorded⟩,words,indices⟩
  | simple ordinary => exact ⟨none,none,⟨running,_,fetch,.simple ordinary⟩,by simp,by simp⟩

end PtxTorchLean.Poisson.PTX.Flow.Observed
