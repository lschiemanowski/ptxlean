import PtxBinary32.Reciprocal
import PtxBinary32.SoftmaxError
import FloatLib.Floats.Formats.BinaryInterchange.Model.Fields.Proof

/-! Actual nearest-even reciprocal and multiplication, with finiteness derived
from input bounds. This module supplies numerical contracts, not a parallel launch. -/
namespace Ptx.Binary32.Normalize
open TorchLean.Floats (round32 eps32)
open FloatLib.Floats.ExecFloat (Binary)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
noncomputable section

/-- Keep the encoded reciprocal as an actual intermediate operand. -/
def Stages (numerator denominator output : Word) : Prop :=
  ∃ reciprocal, Reciprocal.Results denominator reciprocal ∧ Results .mul numerator reciprocal output

private theorem round_fixed (word : Word) (x : ℝ) (value : finiteReal word=some x) : round32 x=x := by
  have spec := Bounds.finiteReal_spec word x value
  have h := Model.roundAt_toReal_eq (Binary.toModel (decode word)) spec.1
  rwa [spec.2] at h

private theorem two_fixed : round32 2=2 := by
  apply round_fixed (0x40000000 : Word)
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 128 0)) = _
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [FloatFormat.binary32, Model.pow2, bpow, binaryRadix, Radix.toReal]

private theorem four_fixed : round32 4=4 := by
  apply round_fixed (0x40800000 : Word)
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 129 0)) = _
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [FloatFormat.binary32, Model.pow2, bpow, binaryRadix, Radix.toReal]

/-- Nonnegativity and range of the rounded reciprocal follow from the denominator. -/
theorem reciprocal_bounds (S : ℝ) (lower : 1/2≤S) :
    0≤round32 (1/S) ∧ round32 (1/S)≤2 := by
  have positive : 0<S := by linarith
  have lo := Model.roundAt_mono FloatFormat.binary32 (div_nonneg (by norm_num : (0:ℝ)≤1) positive.le)
  have hi := Model.roundAt_mono FloatFormat.binary32 ((div_le_iff₀ positive).mpr (by linarith) : 1/S≤2)
  rw [Model.roundAt_zero] at lo
  change round32 (1/S)≤round32 2 at hi
  rw [two_fixed] at hi
  exact ⟨lo,hi⟩

theorem product_range (u S : ℝ) (small : |u|≤2) (lower : 1/2≤S) :
    |Bounds.exactReal .mul u (round32 (1/S))|≤Bounds.maxFinite := by
  obtain ⟨lo,hi⟩ := reciprocal_bounds S lower
  calc
    _ = |u| * round32 (1/S) := by simp only [Bounds.exactReal,abs_mul,abs_of_nonneg lo]
    _ ≤ 2*2 := mul_le_mul small hi lo (by norm_num)
    _ ≤ Bounds.maxFinite := by rw [Bounds.maxFinite_eq]; norm_num

/-- Finiteness, the actual rounded value and both local errors hold for every
permitted encoded reciprocal and multiplication result. -/
theorem correct (numerator denominator output : Word) (u S : ℝ)
    (input : finiteReal numerator=some u) (sum : finiteReal denominator=some S)
    (small : |u|≤2) (lower : 1/2≤S) (allowed : Stages numerator denominator output) :
    finiteReal output=some (round32 (u*round32 (1/S))) ∧
    |round32 (1/S)-1/S|≤eps32 (1/S) ∧
    |round32 (u*round32 (1/S))-u*round32 (1/S)|≤eps32 (u*round32 (1/S)) ∧
    |round32 (u*round32 (1/S))|≤4 := by
  obtain ⟨reciprocal,hr,hm⟩ := allowed
  have real := Reciprocal.results_real denominator reciprocal S sum (by linarith)
    (Reciprocal.half_range S lower) hr
  have out := Bounds.round_of_range .mul numerator reciprocal output u (round32 (1/S))
    input real (product_range u S small lower) hm
  obtain ⟨lo,hi⟩ := reciprocal_bounds S lower
  have mag : |u*round32 (1/S)|≤4 := by
    rw [abs_mul,abs_of_nonneg lo]
    nlinarith
  have upper := Model.roundAt_mono FloatFormat.binary32 (abs_le.mp mag).2
  have below := Model.roundAt_mono FloatFormat.binary32 (abs_le.mp mag).1
  change round32 (u*round32 (1/S))≤round32 4 at upper
  change round32 (-4)≤round32 (u*round32 (1/S)) at below
  rw [four_fixed] at upper
  change Model.roundAt FloatFormat.binary32 (-4)≤round32 (u*round32 (1/S)) at below
  rw [Model.roundAt_neg] at below
  change -round32 4≤round32 (u*round32 (1/S)) at below
  rw [four_fixed] at below
  exact ⟨out,TorchLean.Floats.FP32.round_abs_error _,TorchLean.Floats.FP32.round_abs_error _,abs_le.mpr ⟨below,upper⟩⟩

/-- These are encoded witnesses, not just unconstrained real stage variables. -/
theorem stages_exist (numerator denominator : Word) : ∃ output, Stages numerator denominator output := by
  obtain ⟨reciprocal,hr⟩ := Reciprocal.results_exists denominator
  obtain ⟨output,ho⟩ := results_exists .mul numerator reciprocal
  exact ⟨output,reciprocal,hr,ho⟩

end
end Ptx.Binary32.Normalize
