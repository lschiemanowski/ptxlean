import PtxBinary32.Exponential
import PtxBinary32.ApproximatePolicyChecks

/-! Encoded edge cases and nondeterministic outputs for the partial exponential
provider. These are kernel-checked mathematics, not hardware experiments. -/
namespace Ptx.Binary32.Exponential.Checks
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open FloatLib.Numerics
open FloatLib.Floats.Formats.Flocq
noncomputable section

theorem positive_zero_real : finiteReal (0 : Word) = some 0 := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.posZero FloatFormat.binary32)) = _
  rw [Model.toReal_posZero _ (by decide)]

theorem negative_zero_real : finiteReal (0x80000000 : Word) = some 0 := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.negZero FloatFormat.binary32)) = _
  rw [Model.toReal_negZero _ (by decide)]

theorem signed_zeros (output : Word) :
    (Results 0 output ↔ output = 0x3f800000) ∧
    (Results 0x80000000 output ↔ output = 0x3f800000) :=
  ⟨zero_iff _ _ positive_zero_real, zero_iff _ _ negative_zero_real⟩

/-- The generic allowance must not weaken the source's exact zero special case. -/
theorem zero_neighbor_rejected : ¬ Results 0 0x3f800001 := by
  rw [zero_iff _ _ positive_zero_real]
  decide

theorem signed_infinities (output : Word) :
    (Results 0xff800000 output ↔ output = 0) ∧
    (Results 0x7f800000 output ↔ output = 0x7f800000) :=
  ⟨neg_inf_iff output, pos_inf_iff output⟩

theorem nan_freedom : Results 0x7fc00000 0xffc00001 ∧ ¬ Results 0x7fc00000 0 := by
  rw [nan_iff _ _ (by decide), nan_iff _ _ (by decide)]
  decide

theorem positive_finite_rejected : ¬ Supported 0x3f800000 ∧
    ¬ ∃ output, Results 0x3f800000 output := by
  have h := positive_unsupported _ 1 Approximate.one_real (by norm_num)
  exact ⟨h,by rwa [results_exists_iff]⟩

theorem negative_one_real : finiteReal (0xbf800000 : Word) = some (-1) := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 true 127 0)) = _
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [FloatFormat.binary32, FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent, Model.pow2, bpow, binaryRadix, Radix.toReal]

theorem half_real : finiteReal (0x3f000000 : Word) = some (1/2) := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 126 0)) = _
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [FloatFormat.binary32, FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent, Model.pow2, bpow, binaryRadix, Radix.toReal]

/-- One actual operand admits distinct encodings; no deterministic center is selected. -/
theorem negative_one_multiple_results :
    Results 0xbf800000 0x3f000000 ∧ Results 0xbf800000 0x3f000001 ∧
    (0x3f000000 : Word) ≠ 0x3f000001 := by
  have center := RoundedReal.word_preserves_value 0x3f000000 (1/2) half_real
    (RoundedReal.unit_range (1/2) (by norm_num) (by norm_num))
  have exponent : (2:ℝ)^(-1:ℝ) = 1/2 := by norm_num
  rw [negative_iff _ _ (-1) negative_one_real (by norm_num),
    negative_iff _ _ (-1) negative_one_real (by norm_num), exponent]
  refine ⟨⟨1/2,1/2,center,half_real,?_⟩,
    ⟨1/2,ApproximatePolicyChecks.output,center,ApproximatePolicyChecks.output_real,?_⟩,by decide⟩
  · simp only [sub_self,abs_zero]
    exact mul_nonneg (by norm_num) (le_max_of_le_left (Approximate.ulp_nonnegative _))
  · have h : (2:ℝ)^(-24:ℤ) ≤
        max (TorchLean.Floats.ulp32 (1/2)) (TorchLean.Floats.ulp32 ApproximatePolicyChecks.output) := by
      rw [← ApproximateBounds.ulp_half]
      exact le_max_left _ _
    calc
      _ = (2:ℝ)^(-24:ℤ) := by norm_num [ApproximatePolicyChecks.output]
      _ ≤ 2 * (2:ℝ)^(-24:ℤ) := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

/-- The smallest-magnitude negative operand is supported without flushing it to zero. -/
theorem negative_subnormal_real : finiteReal (0x80000001 : Word) = some (-(2:ℝ)^(-149:ℤ)) := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 true 0 1)) = _
  rw [Model.toReal_ofFields_subnormal _ _ _ (by decide) (by decide)]
  norm_num [FloatFormat.binary32, FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent, Model.pow2, bpow, binaryRadix, Radix.toReal]

theorem negative_subnormal_exists : ∃ output, Results 0x80000001 output := by
  apply results_exists
  exact Or.inr (Or.inr (Or.inr ⟨_,negative_subnormal_real,by norm_num⟩))

end
end Ptx.Binary32.Exponential.Checks
