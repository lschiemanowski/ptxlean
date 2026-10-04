import PoissonPTX.NativeFlowFrame

namespace PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow

def memoryLayout (s : PTX.State) : Nat × Nat × Nat × Nat :=
  (s.globalStart,s.globalBytes,s.sharedStart,s.sharedBytes)

/-- Instructions update bytes and registers, not the launch's allocation bounds. -/
theorem eval_layout (actual : Flow.Observed.Eval ctx i s t access index) :
    memoryLayout t.core=memoryLayout s.core := by
  cases actual with
  | data one =>
    cases one with
    | data one =>
      cases one with
      | ordinary plain execution =>
        cases execution <;> try rfl
        simp [Concurrent.ordinary] at plain
      | load => rfl
      | store => cases ‹Space› <;> rfl
    | _ => rfl
  | simple ordinary =>
    cases i <;> simp_all [Flow.simple,Flow.next,Flow.goto,Flow.halt,memoryLayout,assign,advance]
    all_goals split <;> simp

theorem runs_layout {start : State n}
    (actual : Runs cfg ctx program start events indices final) (aligned : Aligned start.core) :
    ∀ owner, memoryLayout (final.core.lanes owner)=memoryLayout (start.core.lanes owner) := by
  apply runs_lanes (P:=fun owner s => memoryLayout s.core=memoryLayout (start.core.lanes owner)) actual aligned (fun _ => rfl)
  · intro owner i before after access index ready _ step
    exact (eval_layout step).trans ready
  · intro owner before resource ready _
    exact ready

end PtxTorchLean.Poisson.PTX.Concurrent.NativeFlow
