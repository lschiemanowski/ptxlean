import PtxBinary32.ApproximateBounds

/-! A concrete obstruction to treating two ULP conventions as interchangeable.
No exponential instruction or hardware result is asserted by these examples. -/
namespace Ptx.Binary32.ApproximatePolicyChecks
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
open TorchLean.Floats (ulp32 fexp32)

noncomputable abbrev center : ℝ := 1/2-(2:ℝ)^(-25:ℤ)
noncomputable abbrev output : ℝ := 1/2+(2:ℝ)^(-24:ℤ)

theorem center_real : finiteReal (0x3effffff : Word) = some center := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 125 8388607)) = _
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [center, FloatFormat.binary32, Model.pow2, bpow, binaryRadix, Radix.toReal]

theorem output_real : finiteReal (0x3f000001 : Word) = some output := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 126 1)) = _
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [output, FloatFormat.binary32, Model.pow2, bpow, binaryRadix, Radix.toReal]

theorem center_ulp : ulp32 center = (2:ℝ)^(-25:ℤ) := by
  have hm := magnitude_eq_of_bpow_bounds binaryRadix center (-1) (by norm_num [center])
    (by norm_num [center, bpow, binaryRadix, Radix.toReal])
    (by norm_num [center, bpow, binaryRadix, Radix.toReal])
  rw [ulp32, ulp.of_ne_zero _ _ _ (by norm_num [center]), cexp, hm]
  norm_num [fexp32, fltExp, bpow, binaryRadix, Radix.toReal]

theorem output_ulp : ulp32 output = (2:ℝ)^(-24:ℤ) := by
  have hm := magnitude_eq_of_bpow_bounds binaryRadix output 0 (by norm_num [output])
    (by norm_num [output, bpow, binaryRadix, Radix.toReal])
    (by norm_num [output, bpow, binaryRadix, Radix.toReal])
  rw [ulp32, ulp.of_ne_zero _ _ _ (by norm_num [output]), cexp, hm]
  norm_num [fexp32, fltExp, bpow, binaryRadix, Radix.toReal]

/-- Two output ULPs allow this pair; two center ULPs exclude it. -/
theorem output_spacing_not_center_spacing :
    |output-center| ≤ 2*ulp32 output ∧
      ¬ Approximate.WithinULP 2 0x3effffff 0x3f000001 := by
  constructor
  · rw [output_ulp]; norm_num [center, output]
  · rintro ⟨c, hc, c', z, hc', hz, bound⟩
    rw [center_real] at hc hc'
    rw [output_real] at hz
    cases Option.some.inj hc
    cases Option.some.inj hc'
    cases Option.some.inj hz
    rw [center_ulp] at bound
    norm_num [center, output] at bound

end Ptx.Binary32.ApproximatePolicyChecks
