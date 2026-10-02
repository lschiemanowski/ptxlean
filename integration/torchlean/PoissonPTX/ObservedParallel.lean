import PoissonPTX.ObservedReplay

namespace PtxTorchLean.Poisson.PTX.Flow.Parallel

/-- A launch may interleave any running thread. This fragment has no barriers;
its load choices are constrained separately by the recorded byte sources. -/
inductive Runs (ctx : Fin n → Kernel.Context) (program : List Instr) :
    (Fin n → State) → List (Concurrent.Event n) → List (Fin n × IndexSources.Access) → (Fin n → State) → Prop where
  | nil : Runs ctx program s [] [] s
  | cons (step : Observed.Step (ctx thread) program (s thread) t access index)
      (rest : Runs ctx program (Function.update s thread t) words indices u) :
      Runs ctx program s (access.toList.map (Concurrent.Event.data thread)++words)
        (index.toList.map (thread,·)++indices) u

def wordsFor (thread : Fin n) (events : List (Concurrent.Event n)) : List Concurrent.Access :=
  events.filterMap fun event => match event with
    | .data owner a => if owner=thread then some a else none
    | .barrier _ => none

def indicesFor (thread : Fin n) (indices : List (Fin n × IndexSources.Access)) : List IndexSources.Access :=
  indices.filterMap fun (owner,a) => if owner=thread then some a else none

variable {n : Nat} {ctx : Fin n → Kernel.Context} {s t : Fin n → State}
  {words : List (Concurrent.Event n)} {indices : List (Fin n × IndexSources.Access)}

/-- Project a thread from an actual arbitrary interleaving. Its control flow
and all of its observed loads/stores are retained. -/
theorem project (run : Runs ctx program s words indices t) (thread : Fin n) :
    Observed.Runs (ctx thread) program (s thread) (wordsFor thread words) (indicesFor thread indices) (t thread) := by
  induction run with
  | nil => exact .nil
  | @cons selected s middle access index words indices t step rest ih =>
    by_cases same : selected=thread
    · subst selected
      simp only [Function.update_self] at ih
      have one := Observed.Runs.cons step ih
      simpa [wordsFor,indicesFor,List.filterMap_append] using one
    · simpa [wordsFor,indicesFor,List.filterMap_append,Function.update,same,Ne.symm same] using ih

end PtxTorchLean.Poisson.PTX.Flow.Parallel
