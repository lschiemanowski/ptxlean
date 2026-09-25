import PtxBinary32.ReductionRelu
import Mathlib.Algebra.BigOperators.Fin

/-! Zero padding preserves the real sum of products, while the rounded
calculation and its error budget retain every node of the chosen tree. -/
namespace Ptx.Binary32.Reduction

noncomputable def zeroInput : DotError.Input where
  left := 0
  right := 0
  lh := 0
  rh := 0
  l := 0
  r := 0
  el := 0
  er := 0
  leftReal := SquareError.zero_real
  rightReal := SquareError.zero_real
  leftError := by simp
  rightError := by simp
  productRange := by rw [Bounds.maxFinite_eq]; norm_num

noncomputable def paddedInput (f : Fin n → DotError.Input) (column : Nat) : DotError.Input :=
  if h : column<n then f ⟨column,h⟩ else zeroInput

theorem map_balanced (f : α → β) (g : Nat → α) (depth offset : Nat) :
    (balanced depth offset g).map f = balanced depth offset (fun i => f (g i)) := by
  induction depth generalizing offset with
  | zero => rfl
  | succ d ih => simp [balanced,Tree.map,ih]

/-- The ideal real expression is independent of the tree's parenthesization. -/
theorem balanced_ideal (f : Nat → DotError.Input) (depth offset : Nat) :
    ideal (balanced depth offset f) = ∑ i ∈ Finset.range (2^depth), (f (offset+i)).l*(f (offset+i)).r := by
  rw [ideal_leaves,balanced_leaves,List.map_map]
  have ranges : (List.range (2^depth)).toFinset = Finset.range (2^depth) := by
    ext i; simp
  simpa [Function.comp_def,ranges] using
    (List.sum_toFinset (l := List.range (2^depth)) (fun i => (f (offset+i)).l*(f (offset+i)).r) List.nodup_range).symm

/-- Enlarging the finite sum with exact zero products does not alter its value.
No associativity claim about floating-point addition is used here. -/
theorem padded_ideal (f : Fin n → DotError.Input) (depth : Nat) (bound : n≤2^depth) :
    ideal (balanced depth 0 (paddedInput f)) = ∑ i : Fin n, (f i).l*(f i).r := by
  rw [balanced_ideal]
  simp only [Nat.zero_add]
  let term := fun k => (paddedInput f k).l*(paddedInput f k).r
  change (∑ i ∈ Finset.range (2^depth), term i) = _
  have trim : (∑ i ∈ Finset.range n, term i) = ∑ i ∈ Finset.range (2^depth), term i := by
    apply Finset.sum_subset (Finset.range_mono bound)
    intro i _ absent
    have no : ¬i<n := by simpa using absent
    simp [term,paddedInput,no,zeroInput]
  rw [← trim,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [term,paddedInput,i.isLt]

end Ptx.Binary32.Reduction
