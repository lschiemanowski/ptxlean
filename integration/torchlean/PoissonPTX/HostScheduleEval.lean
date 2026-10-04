import PoissonPTX.HostExecution

namespace PtxTorchLean.Poisson.PTX.Host

/-- A deterministic evaluator for testing host decisions. Its supplied step is
explicitly a test double, not evidence of PTX or GPU execution. -/
def evaluate (step : Entry → Memory → Memory) : Plan → Memory → List Entry × Report × Memory
  | .finish report,memory => ([],report,memory)
  | .launch entry next,memory =>
    let (trace,report,final) := evaluate step next (step entry memory)
    (entry::trace,report,final)
  | .inspect next,memory => evaluate step (next memory) memory

/-- Test evaluation follows exactly the same host execution relation, with the
mock launch relation exposed rather than confused with the concrete PTX one. -/
theorem evaluate_execution (step : Entry → Memory → Memory) (plan : Plan) (memory : Memory) :
    Execution (fun entry before after => after=step entry before) plan memory
      (evaluate step plan memory).1 (evaluate step plan memory).2.1 (evaluate step plan memory).2.2 := by
  induction plan generalizing memory with
  | finish report => exact .finish
  | launch entry next ih => exact .launch rfl (ih _)
  | inspect next ih => exact .inspect (ih memory memory)

end PtxTorchLean.Poisson.PTX.Host
