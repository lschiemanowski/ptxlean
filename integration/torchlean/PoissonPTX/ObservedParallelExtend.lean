import PoissonPTX.ObservedParallelExists

namespace PtxTorchLean.Poisson.PTX.Flow.Parallel

/-- Embed the active coordinates into a larger launched thread set. -/
def extend (_enough : n≤m) (active : Fin n → State) (other : Fin m → State) (thread : Fin m) : State :=
  if h : thread.val<n then active ⟨thread.val,h⟩ else other thread

theorem extend_active (enough : n≤m) (active : Fin n → State) (other : Fin m → State) (thread : Fin n) :
    extend enough active other (thread.castLE enough)=active thread := by simp [extend,thread.isLt]

theorem extend_update (enough : n≤m) (active : Fin n → State) (other : Fin m → State)
    (thread : Fin n) (next : State) :
    extend enough (Function.update active thread next) other=
      Function.update (extend enough active other) (thread.castLE enough) next := by
  funext t
  by_cases live : t.val<n
  · have eq : (⟨t.val,live⟩ : Fin n)=thread ↔ t=thread.castLE enough := by simp [Fin.ext_iff]
    simp [extend,live,Function.update,eq]
  · have different : t≠thread.castLE enough := by intro same; subst t; exact live thread.isLt
    simp [extend,live,Function.update_of_ne different]

def renameEvent (rename : Fin n → Fin m) : Concurrent.Event n → Concurrent.Event m
  | .data owner access => .data (rename owner) access
  | .barrier (.arrival key owner) => .barrier (.arrival key (rename owner))
  | .barrier (.completion key) => .barrier (.completion key)

/-- The same actual instructions embed into the larger launch; the additional
threads have not yet taken any steps. -/
theorem extend_run (enough : n≤m) {ctx : Fin n → Kernel.Context} {launchCtx : Fin m → Kernel.Context}
    {start final : Fin n → State} (other : Fin m → State)
    (sameContext : ∀ t, launchCtx (t.castLE enough)=ctx t)
    (run : Runs ctx code start words indices final) :
    Runs launchCtx code (extend enough start other)
      (words.map (renameEvent (Fin.castLE enough)))
      (indices.map (fun (owner,a) => (owner.castLE enough,a))) (extend enough final other) := by
  induction run with
  | nil => exact .nil
  | @cons thread start next access index words indices final step rest ih =>
    have actual : Observed.Step (launchCtx (thread.castLE enough)) code
        (extend enough start other (thread.castLE enough)) next access index := by
      rw [sameContext,extend_active]; exact step
    rw [extend_update] at ih
    simpa only [List.map_append,List.map_map,Function.comp_def,renameEvent] using Runs.cons actual ih

end PtxTorchLean.Poisson.PTX.Flow.Parallel
