import PtxBinary32.GridReference

/-! Concrete current-array reads for constructing witnesses. Candidate runs and
memory admission retain their existing, more general definitions. -/
namespace Ptx.Scalar.Parallel.Grid
inductive ConcreteRuns (cfg : Config n) (program : List Instr) : State groups n → List (Event groups n) → State groups n → Prop
  | nil : ConcreteRuns cfg program s [] s
  | cons (g : Fin groups) (thread : Fin n) (out : Outcome n)
      (step : Parallel.Step (cfg.group g) program none thread (view s g) out)
      (rest : ConcreteRuns cfg program (install s g out.state) events final) :
      ConcreteRuns cfg program s (tag g out.events++events) final

theorem ConcreteRuns.toRuns (run : ConcreteRuns cfg program s events final) : Runs cfg program s events final := by
  induction run with
  | nil => exact .nil
  | cons g t out step _ ih => exact .cons (.issue g t none out step) ih

theorem concrete_runs_append (first : ConcreteRuns cfg program s left middle)
    (second : ConcreteRuns cfg program middle right final) : ConcreteRuns cfg program s (left++right) final := by
  induction first with
  | nil => exact second
  | cons g t out step _ ih => simpa [List.append_assoc] using ConcreteRuns.cons g t out step (ih second)

theorem embed_concrete (g : Fin groups)
    (run : Parallel.ConcreteRuns (cfg.group g) program (view s g) events final) :
    ConcreteRuns cfg program s (tag g events) (install s g final) := by
  generalize startEq : view s g=start at run
  induction run generalizing s with
  | nil =>
    rw [← startEq]
    have same : install s g (view s g)=s := by
      cases s with
      | mk global blocks => simp [install,view,localOf]
    rw [same]; exact .nil
  | @cons thread start out rest final step run ih =>
    rw [← startEq] at step
    have tail := ih (s := install s g out.state) (by simp)
    have same : install (install s g out.state) g final=install s g final := by simp [install,Function.update_idem]
    rw [same] at tail
    simpa [tag,List.map_append] using ConcreteRuns.cons g thread out step tail

theorem Reference.run_concrete (cfg : Config n) (program : List Instr) (s : State groups n)
    (schedule : List (Fin groups × Fin n)) (eligible : Mixed.Eligible cfg.target) :
    ConcreteRuns cfg program s (run cfg program s schedule).2.1 (run cfg program s schedule).1 := by
  induction schedule generalizing s with
  | nil => exact .nil
  | cons pair rest ih => exact .cons pair.1 pair.2 _ (Parallel.Reference.step_sound _ _ _ _ eligible) (ih _)
end Ptx.Scalar.Parallel.Grid
