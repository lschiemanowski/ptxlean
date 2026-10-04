import PoissonPTX.ObservedParallelExtend

namespace PtxTorchLean.Poisson.PTX.Flow.Parallel

/-- Project the first n launched threads without changing their states. -/
def restrict (enough : n≤m) (states : Fin m → α) : Fin n → α := fun t => states (t.castLE enough)

def restrictEvent (n : Nat) : Concurrent.Event m → Option (Concurrent.Event n)
  | .data owner access => if h : owner.val<n then some (.data ⟨owner.val,h⟩ access) else none
  | .barrier _ => none

def restrictIndex (n : Nat) (item : Fin m × IndexSources.Access) : Option (Fin n × IndexSources.Access) :=
  if h : item.1.val<n then some (⟨item.1.val,h⟩,item.2) else none

theorem restrict_update_active (enough : n≤m) (states : Fin m → α) (thread : Fin m)
    (active : thread.val<n) (next : α) :
    restrict enough (Function.update states thread next)=
      Function.update (restrict enough states) ⟨thread.val,active⟩ next := by
  funext t
  have eq : t.castLE enough=thread ↔ t=(⟨thread.val,active⟩ : Fin n) := by simp [Fin.ext_iff]
  by_cases same : t=(⟨thread.val,active⟩ : Fin n) <;> simp [restrict,Function.update,eq,same]

theorem restrict_update_padding (enough : n≤m) (states : Fin m → α) (thread : Fin m)
    (inactive : ¬thread.val<n) (next : α) :
    restrict enough (Function.update states thread next)=restrict enough states := by
  funext t
  have different : t.castLE enough≠thread := by
    intro eq; have same := congrArg Fin.val eq; have := t.isLt; simp only [Fin.val_castLE] at same; omega
  simp only [restrict,Function.update_of_ne different]

/-- Every full interleaving projects to the same active instructions, retaining
all active word and index observations. No scheduling assumption is used. -/
theorem restrict_run (enough : n≤m) {ctx : Fin m → Kernel.Context} {start final : Fin m → State}
    (run : Runs ctx code start words indices final) :
    Runs (restrict enough ctx) code (restrict enough start)
      (words.filterMap (restrictEvent n)) (indices.filterMap (restrictIndex n)) (restrict enough final) := by
  induction run with
  | nil => exact .nil
  | @cons thread start next access index words indices final step rest ih =>
    by_cases active : thread.val<n
    · have owner : (⟨thread.val,active⟩ : Fin n).castLE enough=thread := rfl
      have actual : Observed.Step ((restrict enough ctx) ⟨thread.val,active⟩) code
          ((restrict enough start) ⟨thread.val,active⟩) next access index := step
      rw [restrict_update_active enough start thread active next] at ih
      have joined := Runs.cons actual ih
      simpa only [List.filterMap_append,List.filterMap_map,Function.comp_def,
        restrictEvent,restrictIndex,dite_eq_left active,List.filterMap_eq_map'] using joined
    · rw [restrict_update_padding enough start thread active next] at ih
      simpa only [List.filterMap_append,List.filterMap_map,Function.comp_def,
        restrictEvent,restrictIndex,dite_eq_right active,List.filterMap_none,List.nil_append] using ih

end PtxTorchLean.Poisson.PTX.Flow.Parallel
