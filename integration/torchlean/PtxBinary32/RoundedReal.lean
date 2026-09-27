import PtxBinary32.Approximate
import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Generic

/-! Encode a rounded real under an input-only finite-range guard. This
noncomputable construction supplies witnesses for relational semantics, not an
executable implementation of transcendental arithmetic. -/
namespace Ptx.Binary32.RoundedReal
open FloatLib.Numerics
open FloatLib.Floats.ExecFloat (Binary)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open FloatLib.Floats.Formats.Flocq
open TorchLean.Floats (round32 rnd32 fexp32 eps32)
noncomputable section

/-- The exact integer-power-of-two representation produced by grid rounding. -/
def roundedDyadic (x : ℝ) : FloatLib.Numerics.Dyadic :=
  Dyadic.ofScaledInt (rnd32 (scaledMantissa binaryRadix fexp32 x))
    (cexp binaryRadix fexp32 x)

theorem scaledInt_real (m e : ℤ) :
    (Dyadic.ofScaledInt m e).toReal = (m : ℝ) * (2:ℝ)^e := by
  cases m <;> simp [Dyadic.ofScaledInt, Dyadic.toReal, Dyadic.signedSignificand]

theorem roundedDyadic_real (x : ℝ) : (roundedDyadic x).toReal = round32 x := by
  rw [roundedDyadic, scaledInt_real]
  rfl

theorem round_idempotent (x : ℝ) : round32 (round32 x) = round32 x :=
  round_preserves_generic rnd32 _ (generic_format_round rnd32 x)

theorem round_range (x : ℝ) (range : |x| ≤ Bounds.maxFinite) :
    |round32 x| ≤ Bounds.maxFinite := by
  have hi := Model.roundAt_mono FloatFormat.binary32 (abs_le.mp range).2
  have lo := Model.roundAt_mono FloatFormat.binary32 (abs_le.mp range).1
  have fixed : Model.roundAt FloatFormat.binary32 Bounds.maxFinite = Bounds.maxFinite :=
    Model.roundAt_toReal_eq _ (by decide)
  rw [fixed] at hi
  rw [Model.roundAt_neg, fixed] at lo
  exact abs_le.mpr ⟨lo,hi⟩

/-- Packing the already rounded dyadic may overflow outside the guarded domain. -/
def word (x : ℝ) : Word :=
  (Model.roundDyadic FloatFormat.binary32 (roundedDyadic x)).bits

theorem decode_bits (m : Model FloatFormat.binary32) :
    Binary.toModel (decode m.bits) = m := by
  cases m
  rfl

theorem word_finite (x : ℝ) (range : |x| ≤ Bounds.maxFinite) :
    isFinite (word x) = true := by
  have h := Model.isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite
    FloatFormat.binary32 (by decide) (roundedDyadic x)
    (by rw [roundedDyadic_real]; exact round_range x range)
  change Model.isFinite (Binary.toModel (decode (word x))) = true
  rw [word, decode_bits]
  exact h

theorem word_real (x : ℝ) (range : |x| ≤ Bounds.maxFinite) :
    finiteReal (word x) = some (round32 x) := by
  rw [finiteReal_some _ (word_finite x range)]
  have h := Model.isFinite_roundDyadic_of_isIEEE_of_abs_toReal_le_posMaxFinite
    FloatFormat.binary32 (by decide) (roundedDyadic x)
    (by rw [roundedDyadic_real]; exact round_range x range)
  rw [word, decode_bits]
  apply congrArg some
  exact (Model.toReal_roundDyadic_eq_roundAt _ (by decide) _ h).trans
    (by rw [roundedDyadic_real]; exact round_idempotent x)

theorem exists_word (x : ℝ) (range : |x| ≤ Bounds.maxFinite) :
    ∃ w : Word, finiteReal w = some (round32 x) :=
  ⟨word x, word_real x range⟩

/-- A representable finite input is fixed numerically, including either zero sign. -/
theorem word_preserves_value (w : Word) (x : ℝ) (value : finiteReal w = some x)
    (range : |x| ≤ Bounds.maxFinite) : finiteReal (word x) = some x := by
  rw [word_real x range]
  have spec := Bounds.finiteReal_spec w x value
  have fixed := Model.roundAt_toReal_eq (Binary.toModel (decode w)) spec.1
  rw [spec.2] at fixed
  exact congrArg some fixed

/-- The construction removes the caller-supplied encoded-center premise. -/
def Results (count : ℕ) (ideal : ℝ) (output : Word) : Prop :=
  Approximate.WithinULP count (word ideal) output

theorem results_exists (count : ℕ) (ideal : ℝ) (range : |ideal| ≤ Bounds.maxFinite) :
    ∃ output, Results count ideal output :=
  Approximate.ulp_nonempty (word ideal) (word_finite ideal range) count

theorem results_error (count : ℕ) (ideal : ℝ) (output : Word)
    (range : |ideal| ≤ Bounds.maxFinite) (allowed : Results count ideal output) :
    ∃ z : ℝ, finiteReal output = some z ∧
      |z-ideal| ≤ count * TorchLean.Floats.ulp32 (round32 ideal) + eps32 ideal :=
  Approximate.ulp_error allowed (word_real ideal range)
    (TorchLean.Floats.FP32.round_abs_error ideal)

/-- Unit-interval exact values supply an input-only finite-range certificate. -/
theorem unit_range (x : ℝ) (nonneg : 0 ≤ x) (upper : x ≤ 1) :
    |x| ≤ Bounds.maxFinite := by
  rw [abs_of_nonneg nonneg]
  have : (1:ℝ) ≤ Bounds.maxFinite := by rw [Bounds.maxFinite_eq]; norm_num
  exact upper.trans this

theorem exp2_range (x : ℝ) (nonpos : x ≤ 0) : |(2:ℝ)^x| ≤ Bounds.maxFinite :=
  unit_range _ (Real.rpow_pos_of_pos (by norm_num) x).le
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) nonpos)

theorem reciprocal_range (x : ℝ) (lower : 1 ≤ x) : |1/x| ≤ Bounds.maxFinite :=
  unit_range _ (div_nonneg (by norm_num) (by linarith))
    ((div_le_one (by linarith : 0 < x)).mpr lower)

theorem exp2_results_exists (count : ℕ) (x : ℝ) (nonpos : x ≤ 0) :
    ∃ output, Results count ((2:ℝ)^x) output :=
  results_exists count _ (exp2_range x nonpos)

theorem reciprocal_word_exists (x : ℝ) (lower : 1 ≤ x) :
    ∃ output, finiteReal output = some (round32 (1/x)) :=
  exists_word _ (reciprocal_range x lower)

end
end Ptx.Binary32.RoundedReal
