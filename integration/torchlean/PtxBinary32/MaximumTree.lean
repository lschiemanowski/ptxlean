import PtxBinary32.Maximum
import PtxBinary32.ShiftedExp

/-! The exact binary selection tree. These arithmetic facts do not themselves
assert that threads execute or observe any particular memory values. -/
namespace Ptx.Binary32.Maximum.Tree

def nodeValue (input : Nat → Word) : Nat → Nat → Word
  | 0,t => input t
  | k+1,t => Maximum.choose (nodeValue input k (2*t)) (nodeValue input k (2*t+1))

/-- Every node is an actual word from its own contiguous input subtree. -/
theorem attained (input : Nat → Word) (k t : Nat) :
    ∃ j, j < 2^k ∧ nodeValue input k t = input (t*2^k+j) := by
  induction k generalizing t with
  | zero => exact ⟨0,by decide,by simp [nodeValue]⟩
  | succ k ih =>
    obtain ⟨a,ha,va⟩ := ih (2*t)
    obtain ⟨b,hb,vb⟩ := ih (2*t+1)
    rcases Maximum.choose_mem (nodeValue input k (2*t)) (nodeValue input k (2*t+1)) with h | h
    · refine ⟨a,by rw [pow_succ]; omega,?_⟩
      rw [nodeValue,h,va]
      congr 1
      rw [pow_succ]
      ring
    · refine ⟨2^k+b,by rw [pow_succ]; omega,?_⟩
      rw [nodeValue,h,vb]
      congr 1
      rw [pow_succ]
      ring

/-- Finiteness is required only for the input positions under this node.
Every such real input is bounded above by the selected finite value. -/
theorem subtree_upper (input : Nat → Word) (values : Nat → ℝ) (k t : Nat)
    (finite : ∀j, j<2^k → finiteReal (input (t*2^k+j)) = some (values (t*2^k+j))) :
    ∃ m, finiteReal (nodeValue input k t) = some m ∧
      ∀j, j<2^k → values (t*2^k+j) ≤ m := by
  induction k generalizing t with
  | zero =>
    refine ⟨values t, by simpa [nodeValue] using finite 0 (by decide), ?_⟩
    intro j hj
    have : j=0 := by simpa using hj
    simp [this]
  | succ k ih =>
    have leftIndex (j : Nat) : (2*t)*2^k+j = t*2^(k+1)+j := by rw [pow_succ]; ring
    have rightIndex (j : Nat) : (2*t+1)*2^k+j = t*2^(k+1)+(2^k+j) := by rw [pow_succ]; ring
    have leftFinite : ∀j, j<2^k →
        finiteReal (input ((2*t)*2^k+j)) = some (values ((2*t)*2^k+j)) := by
      intro j hj
      rw [leftIndex]
      exact finite j (by rw [pow_succ]; omega)
    have rightFinite : ∀j, j<2^k →
        finiteReal (input ((2*t+1)*2^k+j)) = some (values ((2*t+1)*2^k+j)) := by
      intro j hj
      rw [rightIndex]
      exact finite (2^k+j) (by rw [pow_succ]; omega)
    obtain ⟨a,ha,upperA⟩ := ih (2*t) leftFinite
    obtain ⟨b,hb,upperB⟩ := ih (2*t+1) rightFinite
    refine ⟨max a b, Maximum.choose_real _ _ _ _ ha hb, ?_⟩
    intro j hj
    by_cases left : j<2^k
    · have h := upperA j left
      rw [leftIndex] at h
      exact h.trans (le_max_left _ _)
    · have bound : j-2^k<2^k := by rw [pow_succ] at hj; omega
      have h := upperB (j-2^k) bound
      rw [rightIndex] at h
      have offset : 2^k+(j-2^k)=j := by omega
      rw [offset] at h
      exact h.trans (le_max_right _ _)

/-- The upper bound is attained by an unchanged input word in the same subtree. -/
theorem subtree_maximum (input : Nat → Word) (values : Nat → ℝ) (k t : Nat)
    (finite : ∀j, j<2^k → finiteReal (input (t*2^k+j)) = some (values (t*2^k+j))) :
    ∃ m, finiteReal (nodeValue input k t) = some m ∧
      (∀j, j<2^k → values (t*2^k+j) ≤ m) ∧
      ∃j, j<2^k ∧ nodeValue input k t = input (t*2^k+j) ∧ m = values (t*2^k+j) := by
  obtain ⟨m,hm,upper⟩ := subtree_upper input values k t finite
  obtain ⟨j,hj,word⟩ := attained input k t
  refine ⟨m,hm,upper,j,hj,word,?_⟩
  rw [word,finite j hj] at hm
  exact (Option.some.inj hm).symm

/-- At the root, exactly the first two-to-the-depth inputs form the row. -/
theorem root_maximum (input : Nat → Word) (values : Nat → ℝ) (depth : Nat)
    (finite : ∀i, i<2^depth → finiteReal (input i) = some (values i)) :
    ∃ m, finiteReal (nodeValue input depth 0) = some m ∧
      (∀i, i<2^depth → values i ≤ m) ∧
      ∃i, i<2^depth ∧ nodeValue input depth 0 = input i ∧ m = values i := by
  simpa using subtree_maximum input values depth 0 (by simpa using finite)

/-- Selecting an existing word preserves any common real-magnitude bound.
There is no positivity requirement on the inputs or on the maximum. -/
theorem magnitude_bound (input : Nat → Word) (values : Nat → ℝ) (k t : Nat) (m M : ℝ)
    (finite : ∀j, j<2^k → finiteReal (input (t*2^k+j)) = some (values (t*2^k+j)))
    (small : ∀j, j<2^k → |values (t*2^k+j)| ≤ M)
    (value : finiteReal (nodeValue input k t) = some m) : |m| ≤ M := by
  obtain ⟨j,hj,word⟩ := attained input k t
  rw [word,finite j hj] at value
  rw [← Option.some.inj value]
  exact small j hj

/-- A bounded finite row supplies every input condition of shifted exponentiation.
The final witness identifies a score attaining the maximum. This is an arithmetic
handoff, not execution or memory admission of a combined softmax kernel. -/
theorem root_shifted_bounds (input : Nat → Word) (values : Nat → ℝ) (depth : Nat)
    (finite : ∀i, i<2^depth → finiteReal (input i) = some (values i))
    (small : ∀i, i<2^depth → |values i| ≤ (2:ℝ)^(124:ℤ)) :
    ∃ m, finiteReal (nodeValue input depth 0) = some m ∧
      (∀i, i<2^depth → ShiftedExp.InputBounds (values i) m) ∧
      ∃i, i<2^depth ∧ nodeValue input depth 0 = input i ∧ m = values i := by
  obtain ⟨m,hm,upper,attainment⟩ := root_maximum input values depth finite
  have bound : |m| ≤ (2:ℝ)^(124:ℤ) :=
    magnitude_bound input values depth 0 m _ (by simpa using finite) (by simpa using small) hm
  exact ⟨m,hm,fun i hi => ⟨upper i hi,small i hi,bound⟩,attainment⟩

end Ptx.Binary32.Maximum.Tree
