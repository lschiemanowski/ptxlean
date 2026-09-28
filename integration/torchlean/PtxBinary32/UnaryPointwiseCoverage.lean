import PtxBinary32.UnaryPointwiseReads

/-! Completion forces the output-store site to have executed in every lane.
This rules out a vacuous stored-output argument based only on possible writes. -/
namespace Ptx.Scalar.UnaryPointwise
open ParallelUnary

private theorem step_store_emits
    (step : ParallelUnary.Step target (program op) candidate selected s next event)
    (instruction : event.instruction=ownStore) :
    ∃effect, event.memory=some effect ∧ effect.kind=.store := by
  obtain ⟨_,_,i,fetch,exec⟩ := step
  have iEq : i=ownStore := (exec_origin exec).2.2.symm.trans instruction
  subst i
  cases exec with
  | scalarNext eval =>
    simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,↓reduceIte] at eval
    split at eval
    · contradiction
    · obtain ⟨rfl,rfl⟩ := Scalar.StepResult.next.inj eval
      exact ⟨_,rfl,rfl⟩
  | scalarHalted eval =>
    simp only [Scalar.eval,Scalar.Instr.plain,Scalar.Guard.eval,Scalar.Operand64.eval,↓reduceIte] at eval
    split at eval <;> contradiction

private theorem run_store_emits
    (run : ParallelUnary.Runs target (program op) s events final)
    (member : event∈events) (instruction : event.instruction=ownStore) :
    ∃effect, event.memory=some effect ∧ effect.kind=.store := by
  induction run with
  | nil => simp at member
  | cons step rest ih =>
    cases member with
    | head => exact step_store_emits step instruction
    | tail _ member => exact ih member

/-- An actual emitted output store exists for every completed lane. -/
theorem completed_store {n common : Nat} {op : Op} {before : List Word}
    {seeds : Fin n→Scalar.State} {events : List (Event n)} {final : ParallelUnary.State n}
    (run : ParallelUnary.Runs target (program op) (initial common before seeds) events final)
    (thread : Fin n) (halted : (final.lanes thread).halted=true) :
    ∃event effect, event∈events ∧ event.thread=thread ∧ event.memory=some effect ∧ effect.kind=.store := by
  have pc := completed_pc run thread halted
  obtain ⟨event,member,owner,site⟩ := ParallelUnary.runs_site run (straight op) thread (storePC op)
    (by simp [cursor,initial]) (by simp [cursor,halted,pc,exitPC])
  have fetch := runs_fetch run member
  rw [site,fetch_store] at fetch
  have instruction : event.instruction=ownStore := (Option.some.inj fetch).symm
  obtain ⟨effect,memory,store⟩ := run_store_emits run member instruction
  exact ⟨event,effect,member,owner,memory,store⟩

end Ptx.Scalar.UnaryPointwise
