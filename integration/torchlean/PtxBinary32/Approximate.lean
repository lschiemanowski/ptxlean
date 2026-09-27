import PtxBinary32Bounds

/-! Finite encoded error neighborhoods. These reusable numerical relations are
not themselves PTX instruction contracts. ULP is evaluated at the center using
the pinned FloatLib convention; source fidelity remains a separate obligation. -/
namespace Ptx.Binary32.Approximate
open TorchLean.Floats (ulp32 eps32 round32)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)

/-- An actual finite center and output, never a fallback real value for NaN. -/
def Within (radius : ℝ) (center output : Word) : Prop :=
  ∃ c z : ℝ, finiteReal center = some c ∧ finiteReal output = some z ∧ |z-c| ≤ radius

theorem center_mem (center : Word) (finite : isFinite center = true) (radius : ℝ)
    (nonneg : 0 ≤ radius) : Within radius center center := by
  exact ⟨_, _, finiteReal_some center finite, finiteReal_some center finite, by simpa using nonneg⟩

theorem nonempty (center : Word) (finite : isFinite center = true) (radius : ℝ)
    (nonneg : 0 ≤ radius) : ∃ output, Within radius center output :=
  ⟨center, center_mem center finite radius nonneg⟩

theorem output_finite (h : Within radius center output) : isFinite output = true := by
  obtain ⟨c,z,hc,hz,_⟩ := h
  exact (Bounds.finiteReal_spec output z hz).1

theorem monotone (h : Within radius center output) (widen : radius ≤ radius') :
    Within radius' center output := by
  obtain ⟨c,z,hc,hz,bound⟩ := h
  exact ⟨c,z,hc,hz,bound.trans widen⟩

theorem total_error (h : Within radius center output)
    (value : finiteReal center = some c) (centerError : |c-ideal| ≤ error) :
    ∃ z : ℝ, finiteReal output = some z ∧ |z-ideal| ≤ radius+error := by
  obtain ⟨c',z,hc,hz,bound⟩ := h
  have same : c'=c := Option.some.inj (hc.symm.trans value)
  subst c'
  exact ⟨z,hz,(abs_sub_le z c ideal).trans (add_le_add bound centerError)⟩

/-- Correct rounding contributes its own error. This premise does not establish
that an arbitrary real rounded center has a finite binary32 encoding. -/
theorem rounded_center_error (h : Within radius center output)
    (value : finiteReal center = some (round32 ideal)) :
    ∃ z : ℝ, finiteReal output = some z ∧ |z-ideal| ≤ radius+eps32 ideal :=
  total_error h value (TorchLean.Floats.FP32.round_abs_error ideal)

def WithinULP (count : ℕ) (center output : Word) : Prop :=
  ∃ c : ℝ, finiteReal center = some c ∧ Within (count * ulp32 c) center output

theorem ulp_nonnegative (x : ℝ) : 0 ≤ ulp32 x :=
  FloatLib.Floats.Formats.Flocq.ulp.nonneg _ _ x

theorem ulp_nonempty (center : Word) (finite : isFinite center = true) (count : ℕ) :
    ∃ output, WithinULP count center output := by
  refine ⟨center, _, finiteReal_some center finite, center_mem center finite _ ?_⟩
  exact mul_nonneg (Nat.cast_nonneg _) (ulp_nonnegative _)

theorem ulp_error (h : WithinULP count center output)
    (value : finiteReal center = some c) (centerError : |c-ideal| ≤ error) :
    ∃ z : ℝ, finiteReal output = some z ∧ |z-ideal| ≤ count * ulp32 c+error := by
  obtain ⟨c',hc,bound⟩ := h
  have same : c'=c := Option.some.inj (hc.symm.trans value)
  subst c'
  exact total_error bound value centerError

theorem one_real : finiteReal (0x3f800000 : Word) = some 1 := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 127 0)) = some 1
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [FloatFormat.binary32, Model.pow2, FloatLib.Floats.Formats.Flocq.bpow,
    FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]

theorem successor_one_real : finiteReal (0x3f800001 : Word) = some (1+(2:ℝ)^(-23:ℤ)) := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 127 1)) = _
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [FloatFormat.binary32, Model.pow2, FloatLib.Floats.Formats.Flocq.bpow,
    FloatLib.Numerics.binaryRadix, FloatLib.Numerics.Radix.toReal]

/-- Two distinct finite results satisfy the same small allowance. -/
theorem multiple_results : (0x3f800000 : Word) ≠ 0x3f800001 ∧
    Within ((2:ℝ)^(-23:ℤ)) 0x3f800000 0x3f800000 ∧
    Within ((2:ℝ)^(-23:ℤ)) 0x3f800000 0x3f800001 := by
  refine ⟨by decide, center_mem _ (by decide) _ (by positivity),
    1, 1+(2:ℝ)^(-23:ℤ), one_real, successor_one_real, ?_⟩
  norm_num

/-- Sign restrictions cannot be recovered from a real-distance condition. -/
theorem signed_zeros : (0 : Word) ≠ 0x80000000 ∧ Within 0 0 0x80000000 := by
  refine ⟨by decide, 0, 0, ?_, ?_, by norm_num⟩
  · rw [finiteReal_some _ (by decide)]
    change some (Model.toReal (Model.posZero FloatFormat.binary32)) = some 0
    rw [Model.toReal_posZero _ (by decide)]
  · rw [finiteReal_some _ (by decide)]
    change some (Model.toReal (Model.negZero FloatFormat.binary32)) = some 0
    rw [Model.toReal_negZero _ (by decide)]

theorem infinity_excluded (radius : ℝ) (center : Word) :
    ¬ Within radius center 0x7f800000 := by
  intro h
  have := output_finite h
  change false = true at this
  contradiction

theorem nan_excluded (radius : ℝ) (center : Word) :
    ¬ Within radius center 0x7fc00000 := by
  intro h
  have := output_finite h
  change false = true at this
  contradiction

end Ptx.Binary32.Approximate
