import PtxBinary32Bounds

/-! Incoming-error propagation and sequentially rounded affine composition.
The encoded result relations remain the arithmetic boundary. -/
namespace Ptx.Binary32.Error

open TorchLean.Floats (eps32)
open TorchLean.Floats.IEEE754.IEEE32Exec (fp32Round)

/-- No separate sign premise is needed for a valid absolute error budget. -/
theorem budget_nonnegative (actual ideal error : ℝ) (bound : |actual-ideal| ≤ error) :
    0 ≤ error := (abs_nonneg _).trans bound

theorem add_propagation (xh yh x y ex ey : ℝ)
    (left : |xh-x| ≤ ex) (right : |yh-y| ≤ ey) :
    |(xh+yh)-(x+y)| ≤ ex+ey := by
  calc
    |(xh+yh)-(x+y)| = |(xh-x)+(yh-y)| := by congr 1; ring
    _ ≤ |xh-x|+|yh-y| := abs_add_le _ _
    _ ≤ ex+ey := add_le_add left right

theorem mul_propagation (xh yh x y ex ey : ℝ)
    (left : |xh-x| ≤ ex) (right : |yh-y| ≤ ey) :
    |xh*yh-x*y| ≤ |x| *ey + |y| *ex + ex*ey := by
  have cross := mul_le_mul left right (abs_nonneg (yh-y)) (budget_nonnegative xh x ex left)
  calc
    |xh*yh-x*y| = |x*(yh-y)+y*(xh-x)+(xh-x)*(yh-y)| := by congr 1; ring
    _ ≤ |x*(yh-y)+y*(xh-x)| + |(xh-x)*(yh-y)| := abs_add_le _ _
    _ ≤ (|x*(yh-y)|+|y*(xh-x)|) + |(xh-x)*(yh-y)| :=
      add_le_add (abs_add_le _ _) (le_refl _)
    _ = (|x| *|yh-y|+|y| *|xh-x|) + |xh-x| *|yh-y| := by simp only [abs_mul]
    _ ≤ |x| *ey + |y| *ex + ex*ey :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left right (abs_nonneg x))
        (mul_le_mul_of_nonneg_left left (abs_nonneg y))) cross

theorem add_results (left right output : Word) (xh yh x y ex ey : ℝ)
    (leftReal : finiteReal left = some xh) (rightReal : finiteReal right = some yh)
    (range : |xh+yh| ≤ Bounds.maxFinite)
    (leftError : |xh-x| ≤ ex) (rightError : |yh-y| ≤ ey)
    (allowed : Results .add left right output) :
    isFinite output = true ∧ ∃ z : ℝ, finiteReal output = some z ∧
      |z-(x+y)| ≤ eps32 (xh+yh)+ex+ey := by
  obtain ⟨finite, z, value, rounding⟩ := Bounds.results_error .add left right output xh yh leftReal rightReal range allowed
  refine ⟨finite, z, value, ?_⟩
  have incoming := add_propagation xh yh x y ex ey leftError rightError
  have triangle := abs_sub_le z (xh+yh) (x+y)
  change |z-(xh+yh)| ≤ eps32 (xh+yh) at rounding
  linarith

theorem mul_results (left right output : Word) (xh yh x y ex ey : ℝ)
    (leftReal : finiteReal left = some xh) (rightReal : finiteReal right = some yh)
    (range : |xh*yh| ≤ Bounds.maxFinite)
    (leftError : |xh-x| ≤ ex) (rightError : |yh-y| ≤ ey)
    (allowed : Results .mul left right output) :
    isFinite output = true ∧ ∃ z : ℝ, finiteReal output = some z ∧
      |z-x*y| ≤ eps32 (xh*yh)+|x| *ey+|y| *ex+ex*ey := by
  obtain ⟨finite, z, value, rounding⟩ := Bounds.results_error .mul left right output xh yh leftReal rightReal range allowed
  refine ⟨finite, z, value, ?_⟩
  have incoming := mul_propagation xh yh x y ex ey leftError rightError
  have triangle := abs_sub_le z (xh*yh) (x*y)
  change |z-(xh*yh)| ≤ eps32 (xh*yh) at rounding
  linarith

theorem add_exists (left right : Word) (xh yh x y ex ey : ℝ)
    (leftReal : finiteReal left = some xh) (rightReal : finiteReal right = some yh)
    (range : |xh+yh| ≤ Bounds.maxFinite)
    (leftError : |xh-x| ≤ ex) (rightError : |yh-y| ≤ ey) :
    ∃ output, Results .add left right output ∧ isFinite output = true ∧
      ∃ z : ℝ, finiteReal output = some z ∧ |z-(x+y)| ≤ eps32 (xh+yh)+ex+ey := by
  obtain ⟨output, allowed⟩ := results_exists .add left right
  exact ⟨output, allowed, add_results left right output xh yh x y ex ey leftReal rightReal range leftError rightError allowed⟩

theorem mul_exists (left right : Word) (xh yh x y ex ey : ℝ)
    (leftReal : finiteReal left = some xh) (rightReal : finiteReal right = some yh)
    (range : |xh*yh| ≤ Bounds.maxFinite)
    (leftError : |xh-x| ≤ ex) (rightError : |yh-y| ≤ ey) :
    ∃ output, Results .mul left right output ∧ isFinite output = true ∧
      ∃ z : ℝ, finiteReal output = some z ∧ |z-x*y| ≤ eps32 (xh*yh)+|x| *ey+|y| *ex+ex*ey := by
  obtain ⟨output, allowed⟩ := results_exists .mul left right
  exact ⟨output, allowed, mul_results left right output xh yh x y ex ey leftReal rightReal range leftError rightError allowed⟩

/-- A conservative second-stage guard obtained only from the exact first-stage
input expression, its local rounding allowance and the bias magnitude. -/
theorem rounded_add_range (product bias : ℝ)
    (range : |product| + eps32 product + |bias| ≤ Bounds.maxFinite) :
    |fp32Round product + bias| ≤ Bounds.maxFinite := by
  have rounding := TorchLean.Floats.FP32.round_abs_error product
  change |fp32Round product - product| ≤ eps32 product at rounding
  have magnitude := abs_sub_le (fp32Round product) product 0
  simp only [sub_zero] at magnitude
  have sum := abs_add_le (fp32Round product) bias
  linarith

/-- Two separate rounded operations sharing the actual intermediate word. -/
def AffineResults (left right bias intermediate output : Word) : Prop :=
  Results .mul left right intermediate ∧ Results .add intermediate bias output

noncomputable def affineBudget (xh yh bh x y ex ey eb : ℝ) : ℝ :=
  eps32 (fp32Round (xh*yh) + bh) + eps32 (xh*yh) + |x| *ey + |y| *ex + ex*ey + eb

/-- All admitted multiply-then-add outputs satisfy the two-rounding error bound.
Both finite stages follow from explicit input-only guards; this is not FMA. -/
theorem affine_results (left right bias intermediate output : Word)
    (xh yh bh x y b ex ey eb : ℝ)
    (leftReal : finiteReal left = some xh) (rightReal : finiteReal right = some yh)
    (biasReal : finiteReal bias = some bh)
    (multiplyRange : |xh*yh| ≤ Bounds.maxFinite)
    (additionRange : |xh*yh| + eps32 (xh*yh) + |bh| ≤ Bounds.maxFinite)
    (leftError : |xh-x| ≤ ex) (rightError : |yh-y| ≤ ey) (biasError : |bh-b| ≤ eb)
    (allowed : AffineResults left right bias intermediate output) :
    isFinite intermediate = true ∧ isFinite output = true ∧
      ∃ z : ℝ, finiteReal output = some z ∧ |z-(x*y+b)| ≤ affineBudget xh yh bh x y ex ey eb := by
  obtain ⟨midFinite, p, midReal, midError⟩ :=
    mul_results left right intermediate xh yh x y ex ey leftReal rightReal multiplyRange leftError rightError allowed.1
  have midRound := Bounds.round_of_range .mul left right intermediate xh yh leftReal rightReal multiplyRange allowed.1
  have peq : p = fp32Round (xh*yh) := Option.some.inj (midReal.symm.trans midRound)
  subst p
  obtain ⟨outFinite, z, outReal, outError⟩ :=
    add_results intermediate bias output (fp32Round (xh*yh)) bh (x*y) b
      (eps32 (xh*yh)+|x| *ey+|y| *ex+ex*ey) eb midReal biasReal
      (rounded_add_range (xh*yh) bh additionRange) midError biasError allowed.2
  refine ⟨midFinite, outFinite, z, outReal, ?_⟩
  unfold affineBudget
  linarith

/-- Nonvacuity uses actual encoded references for both stages, with no supplied
intermediate value or final approximation premise. -/
theorem affine_exists (left right bias : Word) (xh yh bh x y b ex ey eb : ℝ)
    (leftReal : finiteReal left = some xh) (rightReal : finiteReal right = some yh)
    (biasReal : finiteReal bias = some bh)
    (multiplyRange : |xh*yh| ≤ Bounds.maxFinite)
    (additionRange : |xh*yh| + eps32 (xh*yh) + |bh| ≤ Bounds.maxFinite)
    (leftError : |xh-x| ≤ ex) (rightError : |yh-y| ≤ ey) (biasError : |bh-b| ≤ eb) :
    ∃ intermediate output, AffineResults left right bias intermediate output ∧
      isFinite intermediate = true ∧ isFinite output = true ∧
        ∃ z : ℝ, finiteReal output = some z ∧ |z-(x*y+b)| ≤ affineBudget xh yh bh x y ex ey eb := by
  obtain ⟨intermediate, mulAllowed⟩ := results_exists .mul left right
  obtain ⟨output, addAllowed⟩ := results_exists .add intermediate bias
  exact ⟨intermediate, output, ⟨mulAllowed, addAllowed⟩,
    affine_results left right bias intermediate output xh yh bh x y b ex ey eb
      leftReal rightReal biasReal multiplyRange additionRange leftError rightError biasError ⟨mulAllowed, addAllowed⟩⟩

end Ptx.Binary32.Error
