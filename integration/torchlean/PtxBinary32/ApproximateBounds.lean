import PtxBinary32.RoundedReal
import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp

/-! Uniform numerical bounds on the unit interval. These prove properties of
our explicit center-spacing convention, not its identification with PTX. -/
namespace Ptx.Binary32.ApproximateBounds
open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open FloatLib.Floats.Formats.Flocq
open TorchLean.Floats (ulp32 eps32 round32 fexp32)
noncomputable section

theorem ulp_one : ulp32 1 = (2:ℝ)^(-23:ℤ) := by
  have h := ulp_bpow (β := binaryRadix) (fexp := fexp32) 0
  norm_num [bpow, binaryRadix, Radix.toReal, fexp32, fltExp] at h ⊢
  exact h

theorem ulp_half : ulp32 (1/2) = (2:ℝ)^(-24:ℤ) := by
  have h := ulp_bpow (β := binaryRadix) (fexp := fexp32) (-1)
  norm_num [bpow, binaryRadix, Radix.toReal, fexp32, fltExp] at h ⊢
  exact h

theorem ulp_unit (x : ℝ) (nonneg : 0 ≤ x) (upper : x ≤ 1) :
    ulp32 x ≤ (2:ℝ)^(-23:ℤ) := by
  by_cases zero : x = 0
  · subst x
    rw [TorchLean.Floats.ulp32_zero]
    norm_num [bpow, binaryRadix, Radix.toReal]
  · rw [← ulp_one]
    let : MonotoneExp fexp32 := fltMonotoneExp (-149) 24
    exact ulp_mono_pos (lt_of_le_of_ne nonneg (Ne.symm zero)) upper

theorem round_unit (x : ℝ) (nonneg : 0 ≤ x) (upper : x ≤ 1) :
    0 ≤ round32 x ∧ round32 x ≤ 1 := by
  have lo := Model.roundAt_mono FloatFormat.binary32 nonneg
  have hi := Model.roundAt_mono FloatFormat.binary32 upper
  rw [Model.roundAt_zero] at lo
  have one : Model.roundAt FloatFormat.binary32 1 = 1 := by
    have h := Model.roundAt_toReal_eq (Model.posOne FloatFormat.binary32) (by decide)
    rwa [Model.toReal_posOne] at h
  rw [one] at hi
  exact ⟨lo,hi⟩

/-- Includes the center's half-ULP rounding error as a separate contribution. -/
theorem results_error (count : ℕ) (x : ℝ) (output : Word)
    (nonneg : 0 ≤ x) (upper : x ≤ 1) (allowed : RoundedReal.Results count x output) :
    ∃ z : ℝ, finiteReal output = some z ∧
      |z-x| ≤ ((count:ℝ)+1/2)*(2:ℝ)^(-23:ℤ) := by
  obtain ⟨z,hz,bound⟩ := RoundedReal.results_error count x output
    (RoundedReal.unit_range x nonneg upper) allowed
  refine ⟨z,hz,bound.trans ?_⟩
  have rounded := round_unit x nonneg upper
  have allowance := mul_le_mul_of_nonneg_left
    (ulp_unit (round32 x) rounded.1 rounded.2) (Nat.cast_nonneg count : (0:ℝ) ≤ count)
  have rounding : eps32 x ≤ (2:ℝ)^(-23:ℤ)/2 :=
    div_le_div_of_nonneg_right (ulp_unit x nonneg upper) (by norm_num)
  calc
    _ ≤ count * (2:ℝ)^(-23:ℤ) + (2:ℝ)^(-23:ℤ)/2 := add_le_add allowance rounding
    _ = _ := by ring

theorem exp2_error (x : ℝ) (output : Word) (nonpos : x ≤ 0)
    (allowed : RoundedReal.Results 2 ((2:ℝ)^x) output) :
    ∃ z : ℝ, finiteReal output = some z ∧ |z-(2:ℝ)^x| ≤ 5/(2:ℝ)^24 := by
  have h := results_error 2 ((2:ℝ)^x) output
    (Real.rpow_pos_of_pos (by norm_num) x).le
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) nonpos) allowed
  norm_num at h ⊢
  exact h

end
end Ptx.Binary32.ApproximateBounds
