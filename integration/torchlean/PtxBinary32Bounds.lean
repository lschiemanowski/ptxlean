import PtxBinary32
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Semantics

/-! Sufficient input-range conditions for finite binary32 reference arithmetic.
These are conservative bounds, not a characterization of all nonoverflow cases. -/
namespace Ptx.Binary32.Bounds

open FloatLib.Floats.ExecFloat (Binary)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open TorchLean.Floats.IEEE754.IEEE32Exec

noncomputable def maxFinite : ℝ := (Model.posMaxFinite FloatFormat.binary32).toReal

set_option maxRecDepth 4096 in
/-- The conservative guard is exactly binary32's maximum finite magnitude. -/
theorem maxFinite_eq : maxFinite = (2 - (2 : ℝ)^(-23 : ℤ)) * (2 : ℝ)^(127 : ℤ) := by
  unfold maxFinite
  rw [Model.toReal_posMaxFinite]
  change ((8388608 + 8388607 : Nat) : ℝ) * ((2 : ℝ) ^ (104 : ℤ)) = _
  norm_num

/-- A partial real interpretation provides both finiteness and the actual value. -/
theorem finiteReal_spec (word : Word) (x : ℝ) (value : finiteReal word = some x) :
    isFinite word = true ∧ (Binary.toModel (decode word)).toReal = x := by
  unfold finiteReal at value
  split at value
  · exact ⟨by assumption, by simpa using value⟩
  · simp at value

noncomputable def exactReal (op : Operation) (x y : ℝ) : ℝ :=
  match op with | .add => x+y | .mul => x*y

/-- Finiteness is derived from the exact input expression, before rounding. -/
theorem reference_finite (op : Operation) (left right : Word) (x y : ℝ)
    (leftReal : finiteReal left = some x) (rightReal : finiteReal right = some y)
    (range : |exactReal op x y| ≤ maxFinite) :
    isFinite (reference op left right) = true := by
  obtain ⟨leftFinite, leftEq⟩ := finiteReal_spec left x leftReal
  obtain ⟨rightFinite, rightEq⟩ := finiteReal_spec right y rightReal
  cases op with
  | add =>
    have finite := Model.isFinite_add_of_abs_toReal_add_le_posMaxFinite (fmt := FloatFormat.binary32)
      (Binary.toModel (decode left)) (Binary.toModel (decode right)) (by decide)
      leftFinite rightFinite (by
        change |(Binary.toModel (decode left)).toReal + (Binary.toModel (decode right)).toReal| ≤ maxFinite
        rw [leftEq, rightEq]
        exact range)
    simp only [isFinite, reference, decode_encode]
    change Model.isFinite (Binary.toModel (FloatLib.Floats.ExecFloat.add (decode left) (decode right))) = true
    rw [toModel_add]
    exact finite
  | mul =>
    have finite := Model.isFinite_mul_of_abs_mul_le_posMaxFinite (fmt := FloatFormat.binary32)
      (Binary.toModel (decode left)) (Binary.toModel (decode right)) (by decide)
      leftFinite rightFinite (by
        change |(Binary.toModel (decode left)).toReal| * |(Binary.toModel (decode right)).toReal| ≤ maxFinite
        rw [leftEq, rightEq]
        simpa only [exactReal, abs_mul] using range)
    simp only [isFinite, reference, decode_encode]
    change Model.isFinite (Binary.toModel (FloatLib.Floats.ExecFloat.mul (decode left) (decode right))) = true
    rw [toModel_mul]
    exact finite

/-- Input bounds also expose the exact rounded-real meaning of every output. -/
theorem round_of_range (op : Operation) (left right output : Word) (x y : ℝ)
    (leftReal : finiteReal left = some x) (rightReal : finiteReal right = some y)
    (range : |exactReal op x y| ≤ maxFinite) (allowed : Results op left right output) :
    finiteReal output = some (fp32Round (exactReal op x y)) := by
  have finite := reference_finite op left right x y leftReal rightReal range
  have result := results_round op left right output finite allowed
  have leftEq := (finiteReal_spec left x leftReal).2
  have rightEq := (finiteReal_spec right y rightReal).2
  cases op <;> simpa [exact, exactReal, leftEq, rightEq] using result

/-- Every envelope output is finite and obeys the absolute real error bound. -/
theorem results_error (op : Operation) (left right output : Word) (x y : ℝ)
    (leftReal : finiteReal left = some x) (rightReal : finiteReal right = some y)
    (range : |exactReal op x y| ≤ maxFinite) (allowed : Results op left right output) :
    isFinite output = true ∧ ∃ z : ℝ, finiteReal output = some z ∧
      |z - exactReal op x y| ≤ TorchLean.Floats.eps32 (exactReal op x y) := by
  have finite := reference_finite op left right x y leftReal rightReal range
  refine ⟨envelope_finite _ _ finite allowed, ?_⟩
  have bound := results_abs_error op left right output x y leftReal rightReal finite allowed
  cases op <;> exact bound

/-- A finite allowed output exists under the input-range condition. -/
theorem finite_result_exists (op : Operation) (left right : Word) (x y : ℝ)
    (leftReal : finiteReal left = some x) (rightReal : finiteReal right = some y)
    (range : |exactReal op x y| ≤ maxFinite) :
    ∃ output, Results op left right output ∧ isFinite output = true ∧
      ∃ z : ℝ, finiteReal output = some z ∧
        |z - exactReal op x y| ≤ TorchLean.Floats.eps32 (exactReal op x y) := by
  obtain ⟨output, allowed⟩ := results_exists op left right
  exact ⟨output, allowed, results_error op left right output x y leftReal rightReal range allowed⟩

theorem add_range_of_magnitudes (x y A B : ℝ) (left : |x| ≤ A) (right : |y| ≤ B)
    (range : A+B ≤ maxFinite) : |exactReal .add x y| ≤ maxFinite :=
  (abs_add_le x y).trans ((add_le_add left right).trans range)

theorem mul_range_of_magnitudes (x y A B : ℝ) (left : |x| ≤ A) (right : |y| ≤ B)
    (range : A*B ≤ maxFinite) : |exactReal .mul x y| ≤ maxFinite := by
  change |x*y| ≤ maxFinite
  rw [abs_mul]
  exact (mul_le_mul left right (abs_nonneg y) ((abs_nonneg x).trans left)).trans range

/-- Unit-bounded operands provide a simple range certificate for either operation. -/
theorem unit_range (op : Operation) (x y : ℝ) (left : |x| ≤ 1) (right : |y| ≤ 1) :
    |exactReal op x y| ≤ maxFinite := by
  have large : (2 : ℝ) ≤ maxFinite := by rw [maxFinite_eq]; norm_num
  cases op with
  | add => exact add_range_of_magnitudes x y 1 1 left right (by linarith)
  | mul => exact mul_range_of_magnitudes x y 1 1 left right (by linarith)

/-- Binary32 encodings of +1 and -1 have their expected finite real values. -/
theorem positive_one_real : finiteReal (0x3f800000 : Word) = some 1 := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.posOne FloatFormat.binary32)) = some 1
  rw [Model.toReal_posOne]

theorem negative_one_real : finiteReal (0xbf800000 : Word) = some (-1) := by
  rw [finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.neg (Model.posOne FloatFormat.binary32))) = some (-1)
  rw [Model.toReal_neg, Model.toReal_posOne]
  decide

/-- Actual encoded operands, with the finiteness conclusion discharged from
an input bound rather than supplied as an output premise. -/
theorem one_negative_one_results (op : Operation) :
    ∃ output, Results op (0x3f800000 : Word) (0xbf800000 : Word) output ∧
      isFinite output = true ∧ ∃ z : ℝ, finiteReal output = some z ∧
        |z - exactReal op 1 (-1)| ≤ TorchLean.Floats.eps32 (exactReal op 1 (-1)) :=
  finite_result_exists op _ _ 1 (-1) positive_one_real negative_one_real
    (unit_range op 1 (-1) (by norm_num) (by norm_num))

end Ptx.Binary32.Bounds
