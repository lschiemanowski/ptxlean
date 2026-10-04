import PoissonPTX.NativeFlow
import PoissonPTX.ConcurrentHistory

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

variable {n : Nat} {cfg : Config n} {ctx : Fin n → Kernel.Context} {s t : State n}

/-- Ordinary control and data instructions cannot manufacture barrier events.
The existing barrier history proof applies to the actual shared barrier state. -/
theorem step_history
    (actual : Step cfg ctx program selected s out) (aligned : Aligned s.core)
    (origin : History.WaitingOrigin cfg s.core before) :
    History.WaitingOrigin cfg out.state.core (before++out.events) ∧
      History.FreshCompletions before out.events := by
  cases actual with
  | @flow instruction _ next access index running fresh fetch effect =>
    apply History.ordinary_history ⟨(update s selected next).core,access.toList.map (Event.data selected)⟩
    · exact origin
    · rfl
    · rfl
    · intro key
      cases ‹Option Access› <;> simp
  | sync => exact History.synchronize_history _ _ _ _ _ aligned origin

theorem runs_history
    (actual : Runs cfg ctx program s events indices t) (aligned : Aligned s.core)
    (origin : History.WaitingOrigin cfg s.core before) (complete : History.CompleteOrigins before) :
    History.WaitingOrigin cfg t.core (before++events) ∧ History.CompleteOrigins (before++events) := by
  induction actual generalizing before with
  | nil => simpa using And.intro origin complete
  | cons one rest ih =>
    obtain ⟨nextOrigin,newCompletions⟩ := step_history one aligned origin
    have result := ih (step_aligned one aligned) nextOrigin (History.append_complete complete newCompletions)
    simpa only [List.append_assoc] using result

/-- Every completion in the complete native machine has earlier real arrivals
from all participating threads, at exactly the same resource and generation. -/
theorem completed_arrivals (actual : Runs cfg ctx program s events indices t)
    (reset : s.core.barrier=Ptx.Barrier.reset generation) : History.CompleteOrigins events := by
  have aligned : Aligned s.core := by intro thread waiting; simp [reset,Ptx.Barrier.reset] at waiting
  have origin : History.WaitingOrigin cfg s.core [] := by intro thread waiting; simp [reset,Ptx.Barrier.reset] at waiting
  have complete : History.CompleteOrigins ([] : List (Event n)) := by intro c key found; simp at found
  simpa using (runs_history actual aligned origin complete).2

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
