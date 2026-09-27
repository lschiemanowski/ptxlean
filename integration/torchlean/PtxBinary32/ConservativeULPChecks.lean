import PtxBinary32.ConservativeULP
import PtxBinary32.ApproximatePolicyChecks

/-! Checks distinguishing the conservative relation from an accidentally
narrowed policy or an invalid extrapolation to arbitrary ULP counts. -/
namespace Ptx.Binary32.ConservativeULPChecks
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
open TorchLean.Floats (ulp32 fexp32)

/-- The wider policy keeps the previously excluded boundary result. -/
theorem boundary_included : ConservativeULP.Within 2 0x3effffff 0x3f000001 ∧
    ¬ Approximate.WithinULP 2 0x3effffff 0x3f000001 := by
  refine ⟨ConservativeULP.output_included ?_,
    ApproximatePolicyChecks.output_spacing_not_center_spacing.2⟩
  exact ⟨_,_,ApproximatePolicyChecks.center_real,ApproximatePolicyChecks.output_real,
    ApproximatePolicyChecks.output_spacing_not_center_spacing.1⟩

theorem negative_min_real : finiteReal (0x80000001 : Word) = some (-(2:ℝ)^(-149:ℤ)) := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 true 0 1)) = _
  rw [Model.toReal_ofFields_subnormal _ _ _ (by decide) (by decide)]
  norm_num [FloatFormat.binary32, FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent, Model.pow2, bpow, binaryRadix, Radix.toReal]

/-- A distance-only allowance must not silently gain a positivity guarantee. -/
theorem tiny_negative_allowed : ConservativeULP.Within 2 0 0x80000001 := by
  apply ConservativeULP.center_included
  have hz : finiteReal (0:Word) = some 0 := by
    rw [finiteReal_some _ (by decide)]
    change some (Model.toReal (Model.posZero FloatFormat.binary32)) = some 0
    rw [Model.toReal_posZero _ (by decide)]
  refine ⟨0,hz,0,_,hz,negative_min_real,?_⟩
  rw [TorchLean.Floats.ulp32_zero]
  norm_num [bpow,binaryRadix,Radix.toReal]

/-- The maximum policy must not turn real equality into bitwise equality. -/
theorem both_zero_signs : ConservativeULP.Within 0 0 0x80000000 := by
  obtain ⟨c,z,hc,hz,h⟩ := Approximate.signed_zeros.2
  exact ⟨c,z,hc,hz,by simpa using h⟩

theorem infinity_excluded (count : ℕ) (center : Word) :
    ¬ ConservativeULP.Within count center 0x7f800000 := by
  intro h
  have bad := ConservativeULP.output_finite h
  change false = true at bad
  contradiction

/-- The uniform error theorem deliberately specializes to two ULPs: for a large
count, output spacing can admit values far outside the center's unit interval. -/
theorem large_count_requires_care : ConservativeULP.Within 8388608 0 0x40000000 ∧
    (8388608+(1:ℝ)/2)*(2:ℝ)^(-23:ℤ) < 2 := by
  have hz : finiteReal (0:Word) = some 0 := by
    rw [finiteReal_some _ (by decide)]
    change some (Model.toReal (Model.posZero FloatFormat.binary32)) = some 0
    rw [Model.toReal_posZero _ (by decide)]
  have ht : finiteReal (0x40000000:Word) = some 2 := by
    rw [finiteReal_some _ (by decide)]
    change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 128 0)) = _
    rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
    norm_num [FloatFormat.binary32,Model.pow2,bpow,binaryRadix,Radix.toReal]
  have ulp_two : ulp32 2 = (2:ℝ)^(-22:ℤ) := by
    have h := ulp_bpow (β:=binaryRadix) (fexp:=fexp32) 1
    norm_num [bpow,binaryRadix,Radix.toReal,fexp32,fltExp] at h ⊢
    exact h
  refine ⟨ConservativeULP.output_included ⟨0,2,hz,ht,?_⟩,by norm_num⟩
  rw [ulp_two]; norm_num

end Ptx.Binary32.ConservativeULPChecks
