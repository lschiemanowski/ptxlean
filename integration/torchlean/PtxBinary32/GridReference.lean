import PtxBinary32.GridExecution
import PtxBinary32.ParallelReference

/-! An executable selected grid schedule. Concrete current-array reads and
reference floating-point values provide witnesses, not general admission rules. -/
namespace Ptx.Scalar.Parallel.Grid.Reference

def step (cfg : Config n) (program : List Instr) (s : State groups n) (g : Fin groups) (t : Fin n) :
    State groups n × List (Event groups n) × Status :=
  let out := Parallel.Reference.step (cfg.group g) program t (view s g)
  (install s g out.state,tag g out.events,out.status)

def run (cfg : Config n) (program : List Instr) (s : State groups n) :
    List (Fin groups × Fin n) → State groups n × List (Event groups n) × List Status
  | [] => (s,[],[])
  | (g,t)::schedule =>
    let out := step cfg program s g t
    let rest := run cfg program out.1 schedule
    (rest.1,out.2.1++rest.2.1,out.2.2::rest.2.2)

theorem step_sound (cfg : Config n) (program : List Instr) (s : State groups n)
    (g : Fin groups) (t : Fin n) (eligible : Mixed.Eligible cfg.target) :
    Step cfg program s (step cfg program s g t).2.1 (step cfg program s g t).1 :=
  .issue g t none _ (Parallel.Reference.step_sound _ _ _ _ eligible)

theorem run_sound (cfg : Config n) (program : List Instr) (s : State groups n)
    (schedule : List (Fin groups × Fin n)) (eligible : Mixed.Eligible cfg.target) :
    Runs cfg program s (run cfg program s schedule).2.1 (run cfg program s schedule).1 := by
  induction schedule generalizing s with
  | nil => exact .nil
  | cons pair rest ih => exact .cons (step_sound cfg program s pair.1 pair.2 eligible) (ih _)

end Ptx.Scalar.Parallel.Grid.Reference
