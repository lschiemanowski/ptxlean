import PtxBinary32.Parallel

/-! Executions retaining the concrete-array choice for loads. Floating-point
results remain relational. This strengthens an existence witness, not the
candidate machine or its memory-admission criterion. -/
namespace Ptx.Scalar.Parallel

inductive ConcreteRuns (cfg : Config n) (program : List Instr) : State n → List (Event n) → State n → Prop
  | nil : ConcreteRuns cfg program s [] s
  | cons : Step cfg program none thread s out → ConcreteRuns cfg program out.state rest final →
      ConcreteRuns cfg program s (out.events++rest) final

theorem ConcreteRuns.toRuns (run : ConcreteRuns cfg program s events final) : Runs cfg program s events final := by
  induction run with
  | nil => exact .nil
  | cons step _ ih => exact .cons step ih

theorem concrete_runs_append (first : ConcreteRuns cfg program s left middle)
    (second : ConcreteRuns cfg program middle right final) : ConcreteRuns cfg program s (left++right) final := by
  induction first with
  | nil => exact second
  | cons step _ ih => simpa [List.append_assoc] using ConcreteRuns.cons step (ih second)

end Ptx.Scalar.Parallel
