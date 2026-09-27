import PtxBinary32.ApproximateBounds

/-! Boundary checks for the mathematical encoding bridge and explicit ULP scale. -/
namespace Ptx.Binary32.RoundedRealChecks
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open TorchLean.Floats (round32 ulp32)

/-- The finite endpoint, rather than just small exact integers. -/
theorem largest_finite :
    finiteReal (RoundedReal.word Bounds.maxFinite) = some Bounds.maxFinite := by
  have nonneg : 0 ≤ Bounds.maxFinite := by rw [Bounds.maxFinite_eq]; norm_num
  rw [RoundedReal.word_real _ (by rw [abs_of_nonneg nonneg])]
  exact congrArg some (Model.roundAt_toReal_eq _ (by decide))

theorem negative_endpoint :
    finiteReal (RoundedReal.word (-Bounds.maxFinite)) = some (-Bounds.maxFinite) := by
  have nonneg : 0 ≤ Bounds.maxFinite := by rw [Bounds.maxFinite_eq]; norm_num
  rw [RoundedReal.word_real _ (by rw [abs_neg, abs_of_nonneg nonneg])]
  change some (Model.roundAt FloatFormat.binary32 (-Bounds.maxFinite)) = _
  rw [Model.roundAt_neg]
  exact congrArg (fun y : ℝ => some (-y)) (Model.roundAt_toReal_eq _ (by decide))

theorem zero_center : finiteReal (RoundedReal.word 0) = some 0 := by
  rw [RoundedReal.word_real _ (RoundedReal.unit_range 0 (by norm_num) (by norm_num))]
  change some (Model.roundAt FloatFormat.binary32 0) = some 0
  rw [Model.roundAt_zero]

theorem smallest_subnormal_real : finiteReal (1 : Word) = some ((2:ℝ)^(-149:ℤ)) := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 0 1)) = _
  rw [Model.toReal_ofFields_subnormal _ _ _ (by decide) (by decide)]
  norm_num [FloatFormat.binary32, FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent, Model.pow2, FloatLib.Floats.Formats.Flocq.bpow,
    FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]

theorem smallest_subnormal_preserved :
    finiteReal (RoundedReal.word ((2:ℝ)^(-149:ℤ))) = some ((2:ℝ)^(-149:ℤ)) :=
  RoundedReal.word_preserves_value 1 _ smallest_subnormal_real
    (RoundedReal.unit_range _ (by positivity) (by norm_num))

/-- Rounding has a finite witness even when the ideal exponential is not rational. -/
theorem fractional_exponent :
    ∃ output, RoundedReal.Results 2 ((2:ℝ)^(-(1/2:ℝ))) output :=
  RoundedReal.exp2_results_exists 2 _ (by norm_num)

theorem deep_underflow_domain : ∃ output, RoundedReal.Results 2 ((2:ℝ)^(-1000:ℝ)) output :=
  RoundedReal.exp2_results_exists 2 _ (by norm_num)

/-- Above the conservative input guard; do not turn the real grid into an
unbounded finite binary32 domain. -/
theorem out_of_range : ¬ |(2:ℝ)^(128:ℤ)| ≤ Bounds.maxFinite := by
  rw [Bounds.maxFinite_eq]
  norm_num

theorem below_one_real : finiteReal (0x3f7ffffc : Word) = some (1-(2:ℝ)^(-22:ℤ)) := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 126 8388604)) = _
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [FloatFormat.binary32, FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent, Model.pow2, FloatLib.Floats.Formats.Flocq.bpow,
    FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]

/-- At one, two center ULPs include four consecutive encoding steps below one.
Thus a count of encoding steps is a genuinely different contract. -/
theorem center_spacing_not_encoding_distance :
    Approximate.WithinULP 2 0x3f800000 0x3f7ffffc ∧
      (0x3f800000 : Word).toNat-(0x3f7ffffc : Word).toNat = 4 := by
  refine ⟨⟨1, Approximate.one_real, 1, 1-(2:ℝ)^(-22:ℤ),
    Approximate.one_real, below_one_real, ?_⟩, by decide⟩
  rw [ApproximateBounds.ulp_one]
  norm_num

end Ptx.Binary32.RoundedRealChecks
