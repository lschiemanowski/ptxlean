import PtxBinary32.UnaryPointwiseContract

/-! Every allowed array result can be reproduced by the existing fetched
sequential pass. This is a same-output relation, not a restriction on a parallel
schedule. It allows numerical proofs to be reused after parallel admission has
established the operand values and actual output relation. -/
namespace Ptx.Scalar.UnaryPointwise
open SoftmaxStorage

private def patched (before desired : List Word) : Nat → List Word
  | 0 => before
  | k+1 => (patched before desired k).set k desired[k]!

private theorem patched_length (before desired : List Word) (k : Nat) :
    (patched before desired k).length=before.length := by
  induction k with
  | zero => rfl
  | succ k ih => simpa [patched] using ih

private theorem patched_outside (before desired : List Word) (k j : Nat) (outside : k≤j) :
    (patched before desired k)[j]?=before[j]? := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [patched,List.getElem?_set_ne (by omega)]
    exact ih (by omega)

private theorem patched_inside (before desired : List Word) (k j : Nat)
    (same : desired.length=before.length) (inside : j<k) (valid : j<before.length) :
    (patched before desired k)[j]?=desired[j]? := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases last : j=k
    · subst j
      rw [patched,List.getElem?_set_self (by rw [patched_length]; exact valid)]
      exact (some_bang desired k (by omega)).symm
    · rw [patched,List.getElem?_set_ne (by omega)]
      exact ih (by omega)

private theorem patched_eq (spec : Spec op n common before after) :
    patched before after n=after := by
  apply List.ext_getElem?
  intro j
  by_cases hi : j<n
  · by_cases valid : j<before.length
    · exact patched_inside _ _ _ _ spec.1 hi valid
    · have h : before.length≤j := by omega
      simp [List.getElem?_eq_none_iff.mpr (show (patched before after n).length≤j by rw [patched_length]; exact h),
        List.getElem?_eq_none_iff.mpr (show after.length≤j by rw [spec.1]; exact h)]
  · exact (patched_outside _ _ _ _ (by omega)).trans (spec.2.1 j (by omega)).symm

/-- The numerical relation remains nondeterministic: every output allowed by
Spec is realized by actual fetched load/arithmetic/store instructions. -/
theorem sequential_realize (op : Op) (n common : Nat) (before after : List Word)
    (bounds : Bounds n common before) (spec : Spec op n common before after) :
    SoftmaxSweep.Run (sequentialStep op common) n before after := by
  have supported : Scalar.Binary32.SupportedTarget target := by
    norm_num [Scalar.Binary32.SupportedTarget,target]
  have build : ∀k, k≤n → SoftmaxSweep.Run (sequentialStep op common) k before (patched before after k) := by
    intro k hk
    induction k with
    | zero => exact .nil
    | succ k ih =>
      have prior := ih (by omega)
      have vk : SoftmaxMemory.ValidIndex (patched before after k) k := by
        constructor
        · rw [patched_length]; have := bounds.2.2.1; have := bounds.2.2.2.1; omega
        · have := bounds.2.2.1; have := bounds.2.2.2.1; have := bounds.2.2.2.2; omega
      have vc : SoftmaxMemory.ValidIndex (patched before after k) common := by
        constructor
        · rw [patched_length]; exact bounds.2.2.2.1
        · have := bounds.2.2.2.1; have := bounds.2.2.2.2; omega
      have first : (patched before after k)[k]! = before[k]! := bang_eq (patched_outside _ _ _ _ le_rfl)
      have second : (patched before after k)[common]! = before[common]! :=
        bang_eq (patched_outside _ _ _ _ (by have := bounds.2.2.1; omega))
      have allowed := spec.2.2 ⟨k,by omega⟩
      rw [← first,← second] at allowed
      apply SoftmaxSweep.Run.snoc prior
      cases op with
      | shifted => exact SoftmaxMemory.shifted_launch_realize target k common k _ after[k]! supported vk vc vk allowed
      | normalize => exact SoftmaxMemory.normalize_launch_realize target k common k _ after[k]! supported vk vc vk allowed
  simpa only [patched_eq spec] using build n le_rfl

end Ptx.Scalar.UnaryPointwise
