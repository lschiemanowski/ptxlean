import PtxBinary32.RoundedReal
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.DivisionSemantics

/-! Encoded nearest-even reciprocal arithmetic. The future PTX target is the
explicit .rn form; approximate reciprocal interpretation remains separate.
There is no fetched instruction, decoder or target coverage in this module. -/
namespace Ptx.Binary32.Reciprocal
open FloatLib.Floats.ExecFloat (Binary)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open TorchLean.Floats (round32 eps32)

def reference (input : Word) : Word :=
  (Model.div (Model.posOne FloatFormat.binary32) (Model.ofBits (fmt := FloatFormat.binary32) input)).bits

def Results (input output : Word) : Prop := Envelope (reference input) output

instance instDecidableResults (input output : Word) : Decidable (Results input output) := by
  unfold Results
  infer_instance

theorem results_exists (input : Word) : ∃ output, Results input output := envelope_exists _

theorem input_nonzero (input : Word) (x : ℝ) (value : finiteReal input = some x)
    (nonzero : x ≠ 0) : Model.isZero (Model.ofBits (fmt := FloatFormat.binary32) input) = false := by
  cases h : Model.isZero (Model.ofBits (fmt := FloatFormat.binary32) input)
  · rfl
  · have zero := Model.toReal_eq_zero_of_isZero _ h
    have val : Model.toReal (Model.ofBits (fmt := FloatFormat.binary32) input) = x :=
      (Bounds.finiteReal_spec input x value).2
    exact False.elim (nonzero (val.symm.trans zero))

theorem reference_finite (input : Word) (x : ℝ) (value : finiteReal input = some x)
    (nonzero : x ≠ 0) (range : |1/x| ≤ Bounds.maxFinite) :
    isFinite (reference input) = true := by
  have spec : Model.isFinite (Model.ofBits (fmt := FloatFormat.binary32) input) = true ∧
      Model.toReal (Model.ofBits (fmt := FloatFormat.binary32) input) = x :=
    Bounds.finiteReal_spec input x value
  have h := Model.isFinite_div_of_abs_div_le_posMaxFinite
    (Model.posOne FloatFormat.binary32) (Model.ofBits (fmt := FloatFormat.binary32) input) (by decide)
    (by decide) spec.1 (input_nonzero input x value nonzero)
    (by rw [Model.toReal_posOne, spec.2]; exact range)
  change Model.isFinite (Binary.toModel (decode (reference input))) = true
  rw [reference, RoundedReal.decode_bits]
  exact h

theorem reference_real (input : Word) (x : ℝ) (value : finiteReal input = some x)
    (nonzero : x ≠ 0) (range : |1/x| ≤ Bounds.maxFinite) :
    finiteReal (reference input) = some (round32 (1/x)) := by
  rw [finiteReal_some _ (reference_finite input x value nonzero range)]
  rw [reference, RoundedReal.decode_bits]
  apply congrArg some
  have spec : Model.isFinite (Model.ofBits (fmt := FloatFormat.binary32) input) = true ∧
      Model.toReal (Model.ofBits (fmt := FloatFormat.binary32) input) = x :=
    Bounds.finiteReal_spec input x value
  have h := Model.toReal_div_eq_roundAt_of_abs_div_le_posMaxFinite
    (Model.posOne FloatFormat.binary32) (Model.ofBits (fmt := FloatFormat.binary32) input) (by decide)
    (by decide) spec.1 (input_nonzero input x value nonzero)
    (by rw [Model.toReal_posOne, spec.2]; exact range)
  rw [Model.toReal_posOne, spec.2] at h
  exact h

theorem results_real (input output : Word) (x : ℝ) (value : finiteReal input = some x)
    (nonzero : x ≠ 0) (range : |1/x| ≤ Bounds.maxFinite) (allowed : Results input output) :
    finiteReal output = some (round32 (1/x)) := by
  rw [envelope_finite_eq _ _ (reference_finite input x value nonzero range) allowed]
  exact reference_real input x value nonzero range

theorem results_error (input output : Word) (x : ℝ) (value : finiteReal input = some x)
    (nonzero : x ≠ 0) (range : |1/x| ≤ Bounds.maxFinite) (allowed : Results input output) :
    ∃ z : ℝ, finiteReal output = some z ∧ |z-1/x| ≤ eps32 (1/x) :=
  ⟨_, results_real input output x value nonzero range allowed,
    TorchLean.Floats.FP32.round_abs_error _⟩

/-- Sufficient for a softmax denominator whose total error is at most one half. -/
theorem half_range (x : ℝ) (lower : 1/2 ≤ x) : |1/x| ≤ Bounds.maxFinite := by
  have pos : 0 < x := by linarith
  have upper : 1/x ≤ 2 := (div_le_iff₀ pos).mpr (by linarith)
  rw [abs_of_nonneg (div_nonneg (by norm_num) pos.le)]
  exact upper.trans (by rw [Bounds.maxFinite_eq]; norm_num)

theorem finite_result_exists (input : Word) (x : ℝ) (value : finiteReal input = some x)
    (lower : 1/2 ≤ x) :
    ∃ output, Results input output ∧ finiteReal output = some (round32 (1/x)) :=
  ⟨reference input, envelope_self _, reference_real input x value (by linarith) (half_range x lower)⟩

/-- Derive the reciprocal's range from the perturbed denominator, without
assuming a successful reciprocal or its output finiteness. -/
theorem result_exists_of_sum_error (input : Word) (S Z D : ℝ)
    (value : finiteReal input = some S) (exactLower : 1 ≤ Z)
    (error : |S-Z| ≤ D) (small : D ≤ 1/2) :
    ∃ output, Results input output ∧ finiteReal output = some (round32 (1/S)) := by
  apply finite_result_exists input S value
  have := abs_le.mp error
  linarith

end Ptx.Binary32.Reciprocal
