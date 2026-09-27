import PtxBinary32.ExpArgument

/-! Encoded checks of the actual multiply used for base conversion. -/
namespace Ptx.Binary32.ExpArgumentChecks
open ExpArgument
open TorchLean.Floats (round32)

/-- Multiplication by -1 changes the sign of the actual supplied constant. -/
theorem negative_one_product :
    Ptx.Binary32.Results .mul 0xbf800000 constantWord 0xbfb8aa3b := by unfold Ptx.Binary32.Results; decide

theorem zero_product : Ptx.Binary32.Results .mul 0 constantWord 0 := by unfold Ptx.Binary32.Results; decide

/-- A nontrivial input discharges the range condition before either stage. -/
theorem negative_one_stages :
    ∃ product output, Ptx.Binary32.Results .mul 0xbf800000 constantWord product ∧
      finiteReal product = some (round32 (-1*constantValue)) ∧
      FiniteExp2 product output := by
  exact stages_exist _ (-1) Bounds.negative_one_real (by norm_num)
    (bounded_product_range (-1) (by norm_num))

/-- Error around exp(-1) for every permitted output after the concrete multiply.
No single exponential answer is chosen or hard-coded by this check. -/
theorem negative_one_accuracy (output : Word)
    (approximate : FiniteExp2 0xbfb8aa3b output) :
    ∃ z : ℝ, finiteReal output = some z ∧
      |z-Real.exp (-1)| ≤ 5/(2:ℝ)^24 + Real.log 2 * budget (-1) 0 := by
  exact natural_exp_error (-1) (-1) 0 _ _ output Bounds.negative_one_real
    (by norm_num) (by norm_num) (bounded_product_range (-1) (by norm_num))
    (by norm_num) negative_one_product approximate

end Ptx.Binary32.ExpArgumentChecks
