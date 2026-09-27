import PtxBinary32.SoftmaxError
import PtxBinary32.Approximate

/-! Checked boundaries of the numerical contracts, without host float evaluation. -/
namespace Ptx.Numerics.Softmax.Checks
open scoped BigOperators

/-- At the boundary D=1, even nonnegative approximations may erase every weight. -/
theorem zero_denominator_boundary :
    Stages (fun _ : Fin 1 => 1) (fun _ => 0) 0 0 (fun _ => 0) (fun _ => 1) 0 0 (fun _ => 0) ∧
      denominatorBudget (fun _ : Fin 1 => (1:ℝ)) 0 = 1 := by
  exact ⟨denominator_can_be_zero, by norm_num [denominatorBudget]⟩

/-- A small final rounding allowance does not imply an exactly normalized row. -/
theorem permitted_nonunit_sum :
    Stages (fun _ : Fin 2 => 1) (fun _ => 1) 2 (1/2)
      (fun _ => 513/1024) (fun _ => 0) 0 0 (fun _ => 1/1024) ∧
      denominatorBudget (fun _ : Fin 2 => (0:ℝ)) 0 < 1 ∧
      (∑ _i : Fin 2, (513/1024 : ℝ)) ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> intros <;> norm_num
  · norm_num [denominatorBudget]
  · norm_num

/-- The normalization bound is attained in that same two-coordinate example. -/
theorem normalization_bound_attained :
    |(∑ _i : Fin 2, (513/1024 : ℝ))-1| =
      ∑ _i : Fin 2, coordinateBudget 0 (denominatorBudget (fun _ : Fin 2 => 0) 0) 0 (1/1024) := by
  norm_num [coordinateBudget, denominatorBudget]

/-- Zero exponentials can satisfy the small-error contract. Positive exact
weights therefore do not imply positive computed weights. -/
theorem permitted_zero_weight :
    let e : Fin 2 → ℝ := ![1,1/1024]
    let a : Fin 2 → ℝ := ![1,0]
    let delta : Fin 2 → ℝ := ![0,1/1024]
    Stages e a 1 1 a delta 0 0 (fun _ => 0) ∧
      denominatorBudget delta 0 < 1 ∧ (∀ i, 0 < e i) ∧ a 1 = 0 := by
  dsimp
  refine ⟨?_, ?_, ?_, rfl⟩
  · constructor
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_two]
    · norm_num
    · intro i; fin_cases i <;> norm_num
  · norm_num [denominatorBudget, Fin.sum_univ_two]
  · intro i; fin_cases i <;> norm_num

/-- Exact backward arithmetic for a uniform row: incoming [1,0] gives [1/4,-1/4]. -/
theorem backward_uniform_row :
    BackwardStages (fun _ : Fin 2 => 1/2) (fun _ => 1/2)
      ![1,0] ![1,0] (1/2) ![1/2,-1/2] ![1/4,-1/4]
      (fun _ => 0) (fun _ => 0) 0 (fun _ => 0) (fun _ => 0) := by
  constructor
  · intro i; norm_num
  · intro i; norm_num
  · norm_num [Fin.sum_univ_two]
  · intro i; fin_cases i <;> norm_num
  · intro i; fin_cases i <;> norm_num

end Ptx.Numerics.Softmax.Checks
