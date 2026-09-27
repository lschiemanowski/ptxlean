import PtxBinary32.ApproximateBounds

/-! A finite envelope covering two named ULP policies. This is numerical
infrastructure, not a resolution of NVIDIA's undocumented ULP evaluation point. -/
namespace Ptx.Binary32.ConservativeULP
open FloatLib.Numerics
open FloatLib.Floats.Formats.Flocq
open TorchLean.Floats (ulp32 eps32 round32 fexp32)
noncomputable section

/-- Allow the larger spacing at the reference or at the returned value. -/
def Within (count : ℕ) (center output : Word) : Prop :=
  ∃ c z : ℝ, finiteReal center = some c ∧ finiteReal output = some z ∧
    |z-c| ≤ count * max (ulp32 c) (ulp32 z)

/-- The alternative policy measures the allowance at the returned value. -/
def OutputULP (count : ℕ) (center output : Word) : Prop :=
  ∃ c z : ℝ, finiteReal center = some c ∧ finiteReal output = some z ∧
    |z-c| ≤ count * ulp32 z

theorem center_included (h : Approximate.WithinULP count center output) :
    Within count center output := by
  obtain ⟨c,hc,c',z,hc',hz,bound⟩ := h
  have same : c'=c := Option.some.inj (hc'.symm.trans hc)
  subst c'
  exact ⟨c,z,hc,hz,bound.trans (mul_le_mul_of_nonneg_left
    (le_max_left _ _) (Nat.cast_nonneg count))⟩

theorem output_included (h : OutputULP count center output) :
    Within count center output := by
  obtain ⟨c,z,hc,hz,bound⟩ := h
  exact ⟨c,z,hc,hz,bound.trans (mul_le_mul_of_nonneg_left
    (le_max_right _ _) (Nat.cast_nonneg count))⟩

/-- On the real line the maximum envelope is exactly the union of the two
policies, rather than an additional output-range restriction. -/
theorem within_iff (count : ℕ) (center output : Word) :
    Within count center output ↔
      Approximate.WithinULP count center output ∨ OutputULP count center output := by
  constructor
  · rintro ⟨c,z,hc,hz,bound⟩
    rcases le_total (ulp32 c) (ulp32 z) with h | h
    · right; exact ⟨c,z,hc,hz,by simpa [max_eq_right h] using bound⟩
    · left; exact ⟨c,hc,c,z,hc,hz,by simpa [max_eq_left h] using bound⟩
  · intro h; exact h.elim center_included output_included

theorem nonempty (center : Word) (finite : isFinite center = true) (count : ℕ) :
    ∃ output, Within count center output := by
  obtain ⟨output,h⟩ := Approximate.ulp_nonempty center finite count
  exact ⟨output,center_included h⟩

theorem output_finite (h : Within count center output) : isFinite output = true := by
  obtain ⟨_,z,_,hz,_⟩ := h
  exact (Bounds.finiteReal_spec output z hz).1

/-- A global spacing bound, including zero and gradual underflow. -/
theorem ulp_relative (x : ℝ) :
    ulp32 x ≤ max ((2:ℝ)^(-149:ℤ)) (|x| * (2:ℝ)^(-23:ℤ)) := by
  by_cases zero : x = 0
  · subst x
    rw [TorchLean.Floats.ulp32_zero]
    exact le_max_left _ _
  · change ulp binaryRadix fexp32 x ≤ _
    rw [ulp.of_ne_zero _ _ _ zero]
    change bpow binaryRadix (max (magnitude binaryRadix x - 24) (-149)) ≤ _
    rcases le_total (magnitude binaryRadix x - 24) (-149) with h | h
    · rw [max_eq_right h]
      exact le_max_left _ _
    · rw [max_eq_left h]
      apply le_trans _ (le_max_right _ _)
      calc
        bpow binaryRadix (magnitude binaryRadix x - 24) =
            bpow binaryRadix (magnitude binaryRadix x - 1) * (2:ℝ)^(-23:ℤ) := by
          rw [show magnitude binaryRadix x - 24 = (magnitude binaryRadix x - 1) + (-23) by omega,
            bpow.add_exp]
          rfl
        _ ≤ |x| * (2:ℝ)^(-23:ℤ) := mul_le_mul_of_nonneg_right
          (bpow_magnitude_sub_one_le binaryRadix x zero) (by positivity)

/-- A deliberately loose first bound avoids assuming the output lies near one. -/
theorem ulp_coarse (x : ℝ) : ulp32 x ≤ (|x|+1) * (2:ℝ)^(-23:ℤ) := by
  apply (ulp_relative x).trans
  apply max_le
  · norm_num
    linarith [abs_nonneg x]
  · norm_num

/-- Inside (-2,2), including negative values and zero, spacing is at most 2^-23. -/
theorem ulp_below_two (x : ℝ) (small : |x| < 2) : ulp32 x ≤ (2:ℝ)^(-23:ℤ) := by
  by_cases zero : x = 0
  · subst x
    rw [TorchLean.Floats.ulp32_zero]
    norm_num [bpow,binaryRadix,Radix.toReal]
  · have mag := magnitude_le_of_abs_lt_bpow binaryRadix x 1 zero (by
      simpa [bpow,binaryRadix,Radix.toReal] using small)
    change ulp binaryRadix fexp32 x ≤ _
    rw [ulp.of_ne_zero _ _ _ zero]
    change bpow binaryRadix (max (magnitude binaryRadix x - 24) (-149)) ≤ bpow binaryRadix (-23)
    apply (bpow_le_bpow_iff _ _ _).2
    omega

/-- An all-result bound: output magnitude is derived, never assumed. -/
theorem unit_distance (c z : ℝ) (nonneg : 0 ≤ c) (upper : c ≤ 1)
    (allowed : |z-c| ≤ 2 * max (ulp32 c) (ulp32 z)) :
    |z-c| ≤ 2 * (2:ℝ)^(-23:ℤ) := by
  have center := ApproximateBounds.ulp_unit c nonneg upper
  have coarse := ulp_coarse z
  have triangle : |z| ≤ |z-c| + 1 := by
    have := abs_sub_le z c 0
    simp only [sub_zero, abs_of_nonneg nonneg] at this
    exact this.trans (add_le_add_right upper _)
  have loose : max (ulp32 c) (ulp32 z) ≤ (|z|+1)*(2:ℝ)^(-23:ℤ) := by
    apply max_le _ coarse
    apply center.trans
    norm_num
  have distance := allowed.trans (mul_le_mul_of_nonneg_left loose (by norm_num : (0:ℝ) ≤ 2))
  have small : |z| < 2 := by
    norm_num at distance
    linarith
  exact allowed.trans (mul_le_mul_of_nonneg_left
    (max_le center (ulp_below_two z small)) (by norm_num))

/-- Correct rounding is included in addition to the approximate allowance. -/
def Results (ideal : ℝ) (output : Word) : Prop := Within 2 (RoundedReal.word ideal) output

theorem results_exists (x : ℝ) (nonneg : 0 ≤ x) (upper : x ≤ 1) :
    ∃ output, Results x output :=
  nonempty _ (RoundedReal.word_finite x (RoundedReal.unit_range x nonneg upper)) 2

theorem results_error (x : ℝ) (output : Word) (nonneg : 0 ≤ x) (upper : x ≤ 1)
    (allowed : Results x output) :
    ∃ z : ℝ, finiteReal output = some z ∧ |z-x| ≤ 5/(2:ℝ)^24 := by
  obtain ⟨c,z,hc,hz,bound⟩ := allowed
  have same : c = round32 x := Option.some.inj
    (hc.symm.trans (RoundedReal.word_real x (RoundedReal.unit_range x nonneg upper)))
  subst c
  have rounded := ApproximateBounds.round_unit x nonneg upper
  have distance := unit_distance _ _ rounded.1 rounded.2 (by simpa using bound)
  have rounding := TorchLean.Floats.FP32.round_abs_error x
  have eps : eps32 x ≤ (2:ℝ)^(-23:ℤ)/2 :=
    div_le_div_of_nonneg_right (ApproximateBounds.ulp_unit x nonneg upper) (by norm_num)
  refine ⟨z,hz,?_⟩
  have := (abs_sub_le z (round32 x) x).trans (add_le_add distance (rounding.trans eps))
  norm_num at this ⊢
  exact this

theorem exp2_results_exists (x : ℝ) (nonpos : x ≤ 0) :
    ∃ output, Results ((2:ℝ)^x) output :=
  results_exists _ (Real.rpow_pos_of_pos (by norm_num) x).le
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) nonpos)

theorem exp2_error (x : ℝ) (output : Word) (nonpos : x ≤ 0)
    (allowed : Results ((2:ℝ)^x) output) :
    ∃ z : ℝ, finiteReal output = some z ∧ |z-(2:ℝ)^x| ≤ 5/(2:ℝ)^24 :=
  results_error _ output (Real.rpow_pos_of_pos (by norm_num) x).le
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) nonpos) allowed

end
end Ptx.Binary32.ConservativeULP
