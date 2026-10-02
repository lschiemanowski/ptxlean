import PoissonPTX.ControlFlowObserved

namespace PtxTorchLean.Poisson.PTX.Flow.Observed

/-- Recording actual accesses loses no ordinary scalar execution. The load
records use its actual memory bits, including permitted result encodings. -/
theorem data_exists (step : Indexed.Eval op s t) :
    ∃ access index, Indexed.Candidate.Data op s t access index := by
  cases step with
  | data one =>
    cases one with
    | load64 valid => exact ⟨_,_,.data (.load valid)⟩
    | store64 valid => exact ⟨_,_,.data (.store valid)⟩
    | _ => exact ⟨none,none,.data (.ordinary rfl (by constructor <;> assumption))⟩
  | mad32 => exact ⟨none,none,.mad32⟩
  | wide4 => exact ⟨none,none,.wide4⟩
  | load32 valid => exact ⟨none,_,.load32 valid⟩

theorem eval_exists (step : Flow.Eval ctx op s t) : ∃ access index, Eval ctx op s t access index := by
  cases step with
  | data one => obtain ⟨a,i,step⟩ := data_exists one; exact ⟨a,i,.data step⟩
  | simple ordinary => exact ⟨none,none,.simple ordinary⟩

theorem run_exists (run : Flow.Runs ctx program s t) :
    ∃ words indices, Runs ctx program s words indices t := by
  induction run with
  | nil => exact ⟨[],[],.nil⟩
  | @cons s middle t step rest ih =>
    obtain ⟨running,op,fetch,one⟩ := step
    obtain ⟨access,index,execution⟩ := eval_exists one
    obtain ⟨words,indices,tail⟩ := ih
    exact ⟨_,_,.cons ⟨running,op,fetch,execution⟩ tail⟩

end PtxTorchLean.Poisson.PTX.Flow.Observed
