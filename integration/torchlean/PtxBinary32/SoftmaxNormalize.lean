import PtxBinary32.Normalize

/-! Discharge normalization's local error obligations from actual encoded
operands and a separately proved sum error. This is not a composed kernel run. -/
namespace Ptx.Binary32.SoftmaxNormalize
open TorchLean.Floats (round32 eps32)
open Ptx.Numerics.Softmax
open scoped BigOperators
noncomputable section

/-- The upstream error guard bounds actual numerators even when they are negative. -/
theorem numerator_bound (exact approximate delta : Fin n→ℝ) (sigma : ℝ)
    (nonneg : ∀ i, 0≤exact i) (upper : ∀ i, exact i≤1)
    (errors : ∀ i, |approximate i-exact i|≤delta i) (sigmaNonneg : 0≤sigma)
    (small : denominatorBudget delta sigma≤1/2) (i : Fin n) : |approximate i|≤2 := by
  have dn : ∀ j, 0≤delta j := fun j => (abs_nonneg _).trans (errors j)
  have single : delta i≤∑j,delta j := Finset.single_le_sum (fun j _ => dn j) (Finset.mem_univ i)
  have di : delta i≤1/2 := by unfold denominatorBudget at small; linarith
  calc
    |approximate i| ≤ |approximate i-exact i|+|exact i| := by
      simpa using abs_add_le (approximate i-exact i) (exact i)
    _ ≤ delta i+1 := add_le_add (errors i) (by rw [abs_of_nonneg (nonneg i)]; exact upper i)
    _ ≤ 2 := by linarith

/-- Obtain the reciprocal range from the exact denominator and two proved errors. -/
theorem denominator_lower (exact approximate delta : Fin n→ℝ) (S sigma : ℝ)
    (exponential : ∀ i, |approximate i-exact i|≤delta i)
    (summation : |S-∑i,approximate i|≤sigma) (lower : 1≤∑i,exact i)
    (small : denominatorBudget delta sigma≤1/2) : 1/2≤S := by
  have errors := sum_error exact approximate delta exponential
  have bound : |S-∑i,exact i|≤denominatorBudget delta sigma := by
    exact (abs_sub_le S (∑i,approximate i) (∑i,exact i)).trans (add_le_add summation errors)
  have := abs_le.mp bound
  linarith

/-- Every actual normalized word realizes the local stages used by the softmax
error theorem. Reciprocal/product finiteness and errors are conclusions. -/
theorem encoded_stages (exact approximate delta : Fin n→ℝ) (S sigma : ℝ)
    (numerators outputs : Fin n→Word) (denominator : Word)
    (inputs : ∀i, finiteReal (numerators i)=some (approximate i))
    (sumValue : finiteReal denominator=some S)
    (nonneg : ∀i, 0≤exact i) (upper : ∀i, exact i≤1) (lower : 1≤∑i,exact i)
    (exponential : ∀i, |approximate i-exact i|≤delta i)
    (summation : |S-∑i,approximate i|≤sigma)
    (small : denominatorBudget delta sigma≤1/2)
    (runs : ∀i, Normalize.Stages (numerators i) denominator (outputs i)) :
    (∀i, finiteReal (outputs i)=some (round32 (approximate i*round32 (1/S)))) ∧
    Stages exact approximate S (round32 (1/S))
      (fun i => round32 (approximate i*round32 (1/S))) delta sigma (eps32 (1/S))
      (fun i => eps32 (approximate i*round32 (1/S))) := by
  have den := denominator_lower exact approximate delta S sigma exponential summation lower small
  have mag := numerator_bound exact approximate delta sigma nonneg upper exponential
    ((abs_nonneg _).trans summation) small
  have checked := fun i => Normalize.correct (numerators i) denominator (outputs i) (approximate i) S
    (inputs i) sumValue (mag i) den (runs i)
  refine ⟨fun i => (checked i).1,exponential,summation,?_,fun i => (checked i).2.2.1⟩
  exact TorchLean.Floats.FP32.round_abs_error _

/-- Coordinate accuracy follows with the two rounding errors left visible. -/
theorem coordinate_accuracy (exact approximate delta : Fin n→ℝ) (S sigma : ℝ)
    (numerators outputs : Fin n→Word) (denominator : Word)
    (inputs : ∀i, finiteReal (numerators i)=some (approximate i))
    (sumValue : finiteReal denominator=some S)
    (nonneg : ∀i, 0≤exact i) (upper : ∀i, exact i≤1) (lower : 1≤∑i,exact i)
    (exponential : ∀i, |approximate i-exact i|≤delta i)
    (summation : |S-∑i,approximate i|≤sigma)
    (small : denominatorBudget delta sigma≤1/2)
    (runs : ∀i, Normalize.Stages (numerators i) denominator (outputs i)) (i : Fin n) :
    ∃ y, finiteReal (outputs i)=some y ∧
      |y-exact i/(∑j,exact j)|≤coordinateBudget (delta i) (denominatorBudget delta sigma)
        (eps32 (1/S)) (eps32 (approximate i*round32 (1/S))) := by
  obtain ⟨values,stages⟩ := encoded_stages exact approximate delta S sigma numerators outputs denominator
    inputs sumValue nonneg upper lower exponential summation small runs
  exact ⟨_,values i,coordinate_error stages nonneg upper lower (by linarith) i⟩

end
end Ptx.Binary32.SoftmaxNormalize
