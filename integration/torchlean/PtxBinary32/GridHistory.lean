import PtxBinary32.GridExecution
import PtxBinary32.ParallelHistory

/-! Actual group barrier histories are derived from grid instruction steps.
Filtering tags preserves each group's order; no completed phase is assumed. -/
namespace Ptx.Scalar.Parallel.Grid

def project (g : Fin groups) (events : List (Event groups n)) : List (Parallel.Event n) :=
  events.filterMap (fun e => if e.1=g then some e.2 else none)

@[simp] theorem project_append (g : Fin groups) (left right : List (Event groups n)) :
    project g (left++right)=project g left++project g right := by simp [project]
@[simp] theorem project_tag_same (g : Fin groups) (events : List (Parallel.Event n)) :
    project g (tag g events)=events := by simp [project,tag,List.filterMap_map,Function.comp_def]
@[simp] theorem project_tag_other (g h : Fin groups) (events : List (Parallel.Event n)) (different : g≠h) :
    project h (tag g events)=[] := by simp [project,tag,List.filterMap_map,Function.comp_def,different]

/-- Every group's current waiters and all its completed barriers have actual
arrival origins in the projected instruction history. -/
def Origins (cfg : Config n) (s : State groups n) (events : List (Event groups n)) : Prop :=
  ∀ g, History.WaitingOrigin (cfg.group g) (view s g) (project g events) ∧
    History.CompleteOrigins (project g events)

theorem step_origins (step : Step cfg program s added final)
    (aligned : ∀ g, Parallel.Aligned (view s g)) (origins : Origins cfg s before) :
    Origins cfg final (before++added) := by
  cases step with
  | issue g t candidate out step =>
    intro h
    simp only [project_append]
    by_cases eq : h=g
    · subst h
      rw [view_install_same,project_tag_same]
      have result := History.runs_history (Parallel.Runs.cons step Parallel.Runs.nil)
        (aligned g) (origins g).1 (origins g).2
      simpa using result
    · rw [project_tag_other _ _ _ (Ne.symm eq),List.append_nil,view_install_other _ _ _ _ eq]
      exact origins h

theorem runs_origins (run : Runs cfg program s events final)
    (aligned : ∀ g, Parallel.Aligned (view s g)) (origins : Origins cfg s before) :
    Origins cfg final (before++events) := by
  induction run generalizing before with
  | nil => simpa using origins
  | cons step _ ih =>
    simpa [List.append_assoc] using ih (step_aligned step aligned) (step_origins step aligned origins)

theorem completed_arrivals {s final : State groups n} {events : List (Event groups n)}
    (run : Runs cfg program s events final)
    (reset : ∀ g, (s.blocks g).barrier=Barrier.reset generation) (g : Fin groups) :
    History.CompleteOrigins (project g events) := by
  have aligned : ∀ g, Parallel.Aligned (view s g) := by
    intro g t ht
    simp [view,reset,Barrier.reset] at ht
  have origins : Origins cfg s [] := by
    intro g
    constructor
    · intro t ht; simp [view,reset,Barrier.reset] at ht
    · intro c key h; simp [project] at h
  have result := (runs_origins run aligned origins) g
  simpa [project] using result.2

end Ptx.Scalar.Parallel.Grid
