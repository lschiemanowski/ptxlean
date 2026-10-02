import PoissonPTX.ControlFlowObserved
import PoissonPTX.GlobalPublication

namespace PtxTorchLean.Poisson.PTX.Flow.Observed

/-- Apply the global write, if any, of one recorded instruction. -/
def applyAccess (memory : Memory) : Option Concurrent.Access → Memory
  | none => memory
  | some a => if a.space=.global ∧ a.data.store=true then write64 memory a.data.address a.data.value else memory

theorem data_memory (step : Indexed.Candidate.Data op s t access index) :
    t.global=applyAccess s.global access := by
  cases step with
  | data one =>
    cases one with
    | ordinary plain execution => cases execution <;> simp_all [Concurrent.ordinary,applyAccess,assign,advance]
    | load => simp [applyAccess,assign,advance]
    | @store sp addr src s valid => cases sp <;> rfl
  | mad32 => rfl
  | wide4 => rfl
  | load32 => rfl

theorem simple_memory : (simple ctx op s).core.global=s.core.global := by
  cases op <;> simp only [simple]
  all_goals first | rfl | (split <;> rfl)

/-- The freely chosen candidate read bits cannot modify byte memory. Global
memory changes are exactly the actual recorded global writes. -/
theorem step_memory (step : Step ctx program s t access index) :
    t.core.global=applyAccess s.core.global access := by
  obtain ⟨_,_,_,execution⟩ := step
  cases execution with
  | data one => exact data_memory one
  | simple => exact simple_memory

theorem applyAccess_congr (equal : one p=two p) : applyAccess one access p=applyAccess two access p := by
  cases access with
  | none => exact equal
  | some a =>
    simp only [applyAccess]
    split
    · simp only [write64]; split <;> simp_all
    · exact equal

theorem applyAccess_outside
    (outside : ∀ a, access=some a → a.space=.global → a.data.store=true →
      p<a.data.address ∨ a.data.address+8≤p) : applyAccess memory access p=memory p := by
  cases access with
  | none => rfl
  | some a =>
    simp only [applyAccess]
    split
    · rename_i store
      exact write64_outside _ _ _ _ (outside a rfl store.1 store.2)
    · rfl

theorem applyEvent_eq {thread : Fin n} :
    Concurrent.GlobalPublication.publish memory (access.toList.map (Concurrent.Event.data thread))=
      applyAccess memory access := by
  cases access <;> rfl

end PtxTorchLean.Poisson.PTX.Flow.Observed
