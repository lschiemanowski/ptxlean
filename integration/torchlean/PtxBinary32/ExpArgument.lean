import PtxBinary32.ConservativeULP
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Preparing an encoded base-two argument for a natural exponential. The local
multiplication is actual binary32 arithmetic. Neither the shift nor a fetched
exponential instruction is asserted by this numerical bridge. -/
namespace Ptx.Binary32.ExpArgument
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
open TorchLean.Floats (round32 eps32)
noncomputable section

/-- Explicit positive binary32 approximation to 1/log(2). -/
def constantWord : Word := 0x3fb8aa3b

def constantValue : ℝ := 12102203 / 8388608

theorem constant_real : finiteReal constantWord = some constantValue := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 127 3713595)) = _
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [constantValue, FloatFormat.binary32, Model.pow2, bpow, binaryRadix, Radix.toReal]

theorem constant_positive : 0 < constantValue := by norm_num [constantValue]

/-- Keep the mathematical constant error explicit, without a decimal oracle. -/
def constantError : ℝ := |constantValue - 1/Real.log 2|

/-- Sensitivity, constant error, and multiplication rounding are distinct. -/
def budget (shifted shiftError : ℝ) : ℝ :=
  eps32 (shifted*constantValue) + |shifted| *constantError + shiftError / Real.log 2

theorem exp_nonpos_distance (a b : ℝ) (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a-Real.exp b| ≤ |a-b| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.exp) (s := Set.Iic (0:ℝ)) (C := 1)
    (fun x _ => Real.differentiableAt_exp)
    (fun x hx => by simpa only [Real.deriv_exp, Real.norm_eq_abs, Real.abs_exp] using
      (Real.exp_le_one_iff.mpr hx)) (convex_Iic 0) hb ha
  simpa using h

/-- On nonpositive arguments the base-two exponential is log(2)-Lipschitz. -/
theorem exp2_nonpos_distance (a b : ℝ) (ha : a ≤ 0) (hb : b ≤ 0) :
    |(2:ℝ)^a-(2:ℝ)^b| ≤ Real.log 2 * |a-b| := by
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := exp_nonpos_distance (Real.log 2*a) (Real.log 2*b)
    (mul_nonpos_of_nonneg_of_nonpos logpos.le ha)
    (mul_nonpos_of_nonneg_of_nonpos logpos.le hb)
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2), ← mul_sub, abs_mul,
    abs_of_pos logpos] at *
  exact h

theorem base_conversion (x : ℝ) : (2:ℝ)^(x / Real.log 2) = Real.exp x := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
  congr 1
  field_simp

/-- A supplied binary32 product produces a finite, nonpositive argument. The
range guard concerns its exact input expression, not the result to be proved. -/
theorem product_real (input product : Word) (x : ℝ)
    (value : finiteReal input = some x) (nonpos : x ≤ 0)
    (range : |x*constantValue| ≤ Bounds.maxFinite)
    (allowed : Ptx.Binary32.Results .mul input constantWord product) :
    finiteReal product = some (round32 (x*constantValue)) ∧
      round32 (x*constantValue) ≤ 0 := by
  constructor
  · exact Bounds.round_of_range .mul input constantWord product x constantValue
      value constant_real range allowed
  · have h := Model.roundAt_mono FloatFormat.binary32
      (mul_nonpos_of_nonpos_of_nonneg nonpos constant_positive.le)
    rwa [Model.roundAt_zero] at h

/-- A simple sufficient input guard for finite conversion; no output hypothesis. -/
theorem bounded_product_range (x : ℝ) (small : |x| ≤ (2:ℝ)^(126:ℤ)) :
    |x*constantValue| ≤ Bounds.maxFinite := by
  rw [abs_mul,abs_of_pos constant_positive]
  have h := mul_le_mul_of_nonneg_right small constant_positive.le
  apply h.trans
  rw [Bounds.maxFinite_eq]
  norm_num [constantValue]

/-- The caller supplies only a bound on the already shifted input; this theorem
discharges conversion-constant and multiplication errors from actual operands. -/
theorem argument_error (x t shiftError : ℝ) (input product : Word)
    (value : finiteReal input = some x) (range : |x*constantValue| ≤ Bounds.maxFinite)
    (shift : |x-t| ≤ shiftError)
    (allowed : Ptx.Binary32.Results .mul input constantWord product) :
    ∃ a : ℝ, finiteReal product = some a ∧ |a-t/Real.log 2| ≤ budget x shiftError := by
  have value' := Bounds.round_of_range .mul input constantWord product x constantValue
    value constant_real range allowed
  refine ⟨round32 (x*constantValue),value',?_⟩
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have prep : |x*constantValue-t/Real.log 2| ≤
      |x| *constantError+shiftError/Real.log 2 := by
    calc
      _ = |x*(constantValue-1/Real.log 2)+(x-t)/Real.log 2| := by congr 1; ring
      _ ≤ |x*(constantValue-1/Real.log 2)|+|(x-t)/Real.log 2| := abs_add_le _ _
      _ = |x| *constantError+|x-t|/Real.log 2 := by
        rw [abs_mul,abs_div,abs_of_pos logpos]; rfl
      _ ≤ _ := add_le_add_right (div_le_div_of_nonneg_right shift logpos.le) _
  have h := (abs_sub_le (round32 (x*constantValue)) (x*constantValue) (t/Real.log 2)).trans
    (add_le_add (TorchLean.Floats.FP32.round_abs_error _) prep)
  simpa only [budget,add_assoc] using h

/-- Numerical finite branch on the actual encoded operand. Special input cases
and fetched instruction behavior remain outside this relation. -/
def FiniteExp2 (input output : Word) : Prop :=
  ∃ a : ℝ, finiteReal input = some a ∧ a ≤ 0 ∧
    ConservativeULP.Results ((2:ℝ)^a) output

/-- A natural-exponential estimate covering every output allowed by either
named ULP policy, including the explicit base-conversion operations. -/
theorem natural_exp_error (x t shiftError : ℝ) (input product output : Word)
    (value : finiteReal input = some x) (nonpos : x ≤ 0) (idealNonpos : t ≤ 0)
    (range : |x*constantValue| ≤ Bounds.maxFinite) (shift : |x-t| ≤ shiftError)
    (multiply : Ptx.Binary32.Results .mul input constantWord product)
    (approximate : FiniteExp2 product output) :
    ∃ z : ℝ, finiteReal output = some z ∧
      |z-Real.exp t| ≤ 5/(2:ℝ)^24 + Real.log 2 * budget x shiftError := by
  have pr := product_real input product x value nonpos range multiply
  obtain ⟨a,ha,err⟩ := argument_error x t shiftError input product value range shift multiply
  have same : a = round32 (x*constantValue) := Option.some.inj (ha.symm.trans pr.1)
  subst a
  obtain ⟨a,ha,_,approximate⟩ := approximate
  have same : a = round32 (x*constantValue) := Option.some.inj (ha.symm.trans pr.1)
  subst a
  obtain ⟨z,hz,approx⟩ := ConservativeULP.exp2_error _ output pr.2 approximate
  have logpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have sensitivity := exp2_nonpos_distance (round32 (x*constantValue)) (t/Real.log 2)
    pr.2 (div_nonpos_of_nonpos_of_nonneg idealNonpos logpos.le)
  rw [base_conversion] at sensitivity
  exact ⟨z,hz,(abs_sub_le _ _ _).trans (add_le_add approx
    (sensitivity.trans (mul_le_mul_of_nonneg_left err logpos.le)))⟩

/-- Encoded witnesses for both stages, constructed under an input product bound.
This is arithmetic existence, not kernel execution existence. -/
theorem stages_exist (input : Word) (x : ℝ) (value : finiteReal input = some x)
    (nonpos : x ≤ 0) (range : |x*constantValue| ≤ Bounds.maxFinite) :
    ∃ product output, Ptx.Binary32.Results .mul input constantWord product ∧
      finiteReal product = some (round32 (x*constantValue)) ∧
      FiniteExp2 product output := by
  obtain ⟨product,allowed⟩ := Ptx.Binary32.results_exists .mul input constantWord
  have pr := product_real input product x value nonpos range allowed
  obtain ⟨output,h⟩ := ConservativeULP.exp2_results_exists _ pr.2
  exact ⟨product,output,allowed,pr.1,_,pr.1,pr.2,h⟩

end
end Ptx.Binary32.ExpArgument
