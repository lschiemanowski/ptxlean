import PtxBinary32.SoftmaxParallel
import PtxBinary32.SoftmaxPipelineChecks

/-! The parallel composition inherits exact singleton behavior for every admitted
execution, and independently constructs a complete execution from any supported
singleton score. -/
namespace Ptx.Scalar.SoftmaxParallel.Checks
open Parallel Ptx.Binary32
local instance : NeZero (Sum.width 0) := ⟨by norm_num [Sum.width]⟩

theorem singleton_exact (input : Fin (Sum.width 0) → Word) (x : ℝ)
    (finite : finiteReal (input 0)=some x) (small : |x|≤(2:ℝ)^(124:ℤ))
    (run : Run 0 input final) : final[0]?=some (0x3f800000 : Word) :=
  SoftmaxPipeline.Checks.singleton_exact input x finite small (refines run)

theorem singleton_exists (input : Fin (Sum.width 0) → Word) (x : ℝ)
    (finite : finiteReal (input 0)=some x) (small : |x|≤(2:ℝ)^(124:ℤ)) :
    ∃final, Run 0 input final ∧ final[0]?=some (0x3f800000 : Word) := by
  obtain ⟨final,run,one⟩ := SoftmaxPipeline.Checks.singleton_exists input x finite small
  exact ⟨final,of_reference (by unfold Sum.Bounds; decide) run,one⟩

end Ptx.Scalar.SoftmaxParallel.Checks
