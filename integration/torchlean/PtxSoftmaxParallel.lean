import PtxBinary32.SoftmaxParallel
import PtxSoftmaxPipeline

/-! Stored outputs of the parallel forward pipeline satisfy the same TorchLean
accuracy contract as the reference composition. The output refinement preserves
all admitted schedules and arithmetic results. -/
namespace PtxTorchLean.SoftmaxParallel
open Ptx Ptx.Binary32 Ptx.Scalar.Parallel

/-- Universal stored-output accuracy, under exactly the reference input guard. -/
theorem correct (d : Nat) (bound : d≤10)
    (input : Fin (Sum.width d) → Word) (values : Fin (Sum.width d) → ℝ)
    (finite : ∀i, finiteReal (input i)=some (values i))
    (small : ∀i, |values i|≤(2:ℝ)^(124:ℤ))
    (guard : SoftmaxPipeline.AccuracyGuard d values)
    (run : Scalar.SoftmaxParallel.Run d input final) :
    SoftmaxPipeline.Accurate d input values final :=
  SoftmaxPipeline.correct d bound input values finite small guard
    (Scalar.SoftmaxParallel.refines run)

/-- Existence is constructed from original scores; accuracy remains a theorem
about the completed execution rather than a field in its definition. -/
theorem accurate_execution_exists (d : Nat) (bound : d≤10)
    (input : Fin (Sum.width d) → Word) (values : Fin (Sum.width d) → ℝ)
    (finite : ∀i, finiteReal (input i)=some (values i))
    (small : ∀i, |values i|≤(2:ℝ)^(124:ℤ))
    (guard : SoftmaxPipeline.AccuracyGuard d values) :
    ∃final, Scalar.SoftmaxParallel.Run d input final ∧
      SoftmaxPipeline.Accurate d input values final := by
  obtain ⟨final,run⟩ := Scalar.SoftmaxParallel.execution_exists d bound input values finite small
  exact ⟨final,run,correct d bound input values finite small guard run⟩

end PtxTorchLean.SoftmaxParallel
