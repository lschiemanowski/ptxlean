import PtxBinary32.Exponential

/-! An encoded shifted exponential using exact negation, rounded addition,
rounded base conversion, and the bounded approximate exponential provider.
The bounds below concern the original inputs; intermediate finiteness and sign
are conclusions. This module establishes arithmetic, not program execution. -/
namespace Ptx.Binary32.ShiftedExp
open FloatLib.Floats.ExecFloat (Binary)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
open TorchLean.Floats (round32 eps32)
noncomputable section

/-- A conservative input-only guard: the score is no greater than the supplied
maximum, and both finite real values have magnitude at most two to the 124th. -/
def InputBounds (x m : ℝ) : Prop :=
  x ≤ m ∧ |x| ≤ (2:ℝ)^(124:ℤ) ∧ |m| ≤ (2:ℝ)^(124:ℤ)

private theorem round_fixed (word : Word) (x : ℝ)
    (value : finiteReal word = some x) : round32 x = x := by
  have spec := Bounds.finiteReal_spec word x value
  have fixed := Model.roundAt_toReal_eq (Binary.toModel (decode word)) spec.1
  rwa [spec.2] at fixed

private theorem bound_fixed : round32 ((2:ℝ)^(126:ℤ)) = (2:ℝ)^(126:ℤ) := by
  apply round_fixed (0x7e800000 : Word)
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 253 0)) = _
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [FloatFormat.binary32, Model.pow2, bpow, binaryRadix, Radix.toReal]

/-- Multiplication by encoded minus one is exact numerically for a finite
bounded maximum, including signed zero. No bitwise zero-sign claim is needed. -/
theorem negative_real (maximum negative : Word) (m : ℝ)
    (value : finiteReal maximum = some m) (small : |m| ≤ (2:ℝ)^(124:ℤ))
    (negate : Ptx.Binary32.Results .mul maximum 0xbf800000 negative) :
    finiteReal negative = some (-m) := by
  have range : |Bounds.exactReal .mul m (-1)| ≤ Bounds.maxFinite := by
    simp only [Bounds.exactReal, mul_neg_one, abs_neg]
    exact small.trans (by rw [Bounds.maxFinite_eq]; norm_num)
  have result := Bounds.round_of_range .mul maximum 0xbf800000 negative m (-1)
    value Bounds.negative_one_real range negate
  change finiteReal negative = some (round32 (m * (-1))) at result
  rw [mul_neg_one] at result
  have fixed : round32 (-m) = -m := by
    change Model.roundAt FloatFormat.binary32 (-m) = -m
    rw [Model.roundAt_neg]
    exact congrArg Neg.neg (round_fixed maximum m value)
  rwa [fixed] at result

/-- The two actual arithmetic operations produce the rounded subtraction.
Finiteness, a nonpositive result, the conversion range, and rounding error all
follow from the original inputs. -/
theorem shift_real (input maximum negative shifted : Word) (x m : ℝ)
    (inputValue : finiteReal input = some x) (maximumValue : finiteReal maximum = some m)
    (bounds : InputBounds x m)
    (negate : Ptx.Binary32.Results .mul maximum 0xbf800000 negative)
    (shift : Ptx.Binary32.Results .add input negative shifted) :
    finiteReal negative = some (-m) ∧
    finiteReal shifted = some (round32 (x-m)) ∧
    round32 (x-m) ≤ 0 ∧ |round32 (x-m)| ≤ (2:ℝ)^(126:ℤ) ∧
    |round32 (x-m)-(x-m)| ≤ eps32 (x-m) := by
  have negValue := negative_real maximum negative m maximumValue bounds.2.2 negate
  have small : |x-m| ≤ (2:ℝ)^(126:ℤ) := by
    calc
      |x-m| ≤ |x|+|m| := abs_sub x m
      _ ≤ (2:ℝ)^(124:ℤ)+(2:ℝ)^(124:ℤ) := add_le_add bounds.2.1 bounds.2.2
      _ ≤ (2:ℝ)^(126:ℤ) := by norm_num
  have range : |Bounds.exactReal .add x (-m)| ≤ Bounds.maxFinite := by
    change |x + -m| ≤ Bounds.maxFinite
    rw [← sub_eq_add_neg]
    exact small.trans (by rw [Bounds.maxFinite_eq]; norm_num)
  have value := Bounds.round_of_range .add input negative shifted x (-m)
    inputValue negValue range shift
  change finiteReal shifted = some (round32 (x + -m)) at value
  rw [← sub_eq_add_neg] at value
  have nonpos : round32 (x-m) ≤ 0 := by
    have h := Model.roundAt_mono FloatFormat.binary32 (sub_nonpos.mpr bounds.1)
    rwa [Model.roundAt_zero] at h
  have hi := Model.roundAt_mono FloatFormat.binary32 (abs_le.mp small).2
  have lo := Model.roundAt_mono FloatFormat.binary32 (abs_le.mp small).1
  change round32 (x-m) ≤ round32 ((2:ℝ)^(126:ℤ)) at hi
  rw [bound_fixed] at hi
  rw [Model.roundAt_neg] at lo
  change -round32 ((2:ℝ)^(126:ℤ)) ≤ round32 (x-m) at lo
  rw [bound_fixed] at lo
  exact ⟨negValue,value,nonpos,abs_le.mpr ⟨lo,hi⟩,
    TorchLean.Floats.FP32.round_abs_error (x-m)⟩

/-- Every output admitted by the four arithmetic stages obeys this absolute
error bound relative to the real shifted exponential. The approximate stage
keeps all outputs of the existing conservative ULP envelope. -/
theorem error (input maximum negative shifted product output : Word) (x m : ℝ)
    (inputValue : finiteReal input = some x) (maximumValue : finiteReal maximum = some m)
    (bounds : InputBounds x m)
    (negate : Ptx.Binary32.Results .mul maximum 0xbf800000 negative)
    (shift : Ptx.Binary32.Results .add input negative shifted)
    (multiply : Ptx.Binary32.Results .mul shifted ExpArgument.constantWord product)
    (approximate : Exponential.Results product output) :
    ∃ z : ℝ, finiteReal output = some z ∧
      |z-Real.exp (x-m)| ≤ 5/(2:ℝ)^24 + Real.log 2 *
        ExpArgument.budget (round32 (x-m)) (eps32 (x-m)) := by
  have h := shift_real input maximum negative shifted x m inputValue maximumValue bounds negate shift
  have range := ExpArgument.bounded_product_range _ h.2.2.2.1
  have productValue := ExpArgument.product_real shifted product _ h.2.1 h.2.2.1 range multiply
  exact ExpArgument.natural_exp_error _ (x-m) _ shifted product output h.2.1 h.2.2.1
    (sub_nonpos.mpr bounds.1) range h.2.2.2.2 multiply
    (Exponential.finiteExp2 product output _ productValue.1 approximate)

/-- Equal finite scores produce exactly encoded positive one, including inputs
with different zero signs. The intermediate zero values are derived from the
actual arithmetic relations rather than supplied as hypotheses. -/
theorem equal_scores (input maximum negative shifted product output : Word) (m : ℝ)
    (inputValue : finiteReal input = some m) (maximumValue : finiteReal maximum = some m)
    (small : |m| ≤ (2:ℝ)^(124:ℤ))
    (negate : Ptx.Binary32.Results .mul maximum 0xbf800000 negative)
    (shift : Ptx.Binary32.Results .add input negative shifted)
    (multiply : Ptx.Binary32.Results .mul shifted ExpArgument.constantWord product)
    (approximate : Exponential.Results product output) : output = 0x3f800000 := by
  have h := shift_real input maximum negative shifted m m inputValue maximumValue
    ⟨le_rfl,small,small⟩ negate shift
  have zeroRound : round32 0 = 0 := Model.roundAt_zero FloatFormat.binary32
  have shiftedZero : finiteReal shifted = some 0 := by
    simpa only [sub_self,zeroRound] using h.2.1
  have productValue := ExpArgument.product_real shifted product 0 shiftedZero le_rfl
    (ExpArgument.bounded_product_range 0 (by norm_num)) multiply
  have productZero : finiteReal product = some 0 := by
    simpa only [zero_mul,zeroRound] using productValue.1
  exact (Exponential.zero_iff product output productZero).mp approximate

/-- Encoded witnesses exist for every stage under the input-only bounds.
This is numerical existence; a fetched program requires a separate proof. -/
theorem stages_exist (input maximum : Word) (x m : ℝ)
    (inputValue : finiteReal input = some x) (maximumValue : finiteReal maximum = some m)
    (bounds : InputBounds x m) :
    ∃ negative shifted product output,
      Ptx.Binary32.Results .mul maximum 0xbf800000 negative ∧
      Ptx.Binary32.Results .add input negative shifted ∧
      Ptx.Binary32.Results .mul shifted ExpArgument.constantWord product ∧
      Exponential.Results product output := by
  obtain ⟨negative,negate⟩ := Ptx.Binary32.results_exists .mul maximum 0xbf800000
  obtain ⟨shifted,shift⟩ := Ptx.Binary32.results_exists .add input negative
  have h := shift_real input maximum negative shifted x m inputValue maximumValue bounds negate shift
  obtain ⟨product,multiply⟩ := Ptx.Binary32.results_exists .mul shifted ExpArgument.constantWord
  have productValue := ExpArgument.product_real shifted product _ h.2.1 h.2.2.1
    (ExpArgument.bounded_product_range _ h.2.2.2.1) multiply
  obtain ⟨output,approximate⟩ := Exponential.results_exists product
    (Or.inr (Or.inr (Or.inr ⟨_,productValue.1,productValue.2⟩)))
  exact ⟨negative,shifted,product,output,negate,shift,multiply,approximate⟩

end
end Ptx.Binary32.ShiftedExp
