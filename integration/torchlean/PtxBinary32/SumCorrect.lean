import PtxBinary32.SumExecution
import PtxBinary32.SumTree

/-! The parallel sum's relational arithmetic has a finite real interpretation
for signed inputs of magnitude at most two. All intermediate range obligations
are discharged by the checked arithmetic tree. -/
namespace Ptx.Scalar.Parallel.Sum
open Ptx.Binary32
open scoped BigOperators
noncomputable section

/-- Extend a finite row for the subtree API; only in-range positions are used. -/
def valuesAt (d : Nat) (values : Fin (width d) → ℝ) (j : Nat) : ℝ :=
  (List.ofFn values)[j]!

def rounded (d : Nat) (values : Fin (width d) → ℝ) : ℝ :=
  SumTree.rounded (valuesAt d values) d 0

theorem ideal_eq_sum (d : Nat) (values : Fin (width d) → ℝ) :
    SumTree.ideal (valuesAt d values) d 0=∑i,values i := by
  rw [SumTree.ideal_sum]
  have same : (List.range (2^d)).map (fun j => valuesAt d values (0+j)) = List.ofFn values := by
    apply List.ext_getElem (by simp only [List.length_map,List.length_range,List.length_ofFn]; rfl)
    intro j hj hj'
    have h : j<width d := by simpa only [List.length_ofFn] using hj'
    simp [valuesAt,List.getElem!_eq_getElem?_getD,h]
  rw [same,List.sum_ofFn]

/-- Every permitted output is the prescribed rounded sum with a derived
absolute error, including when some encoded approximate exponentials are negative. -/
theorem output_accuracy (d : Nat) (bound : Bounds d)
    (input : Fin (width d) → Word) (values : Fin (width d) → ℝ) (out : Word)
    (finite : ∀i, finiteReal (input i)=some (values i))
    (small : ∀i, |values i|≤2) (allowed : Output d input out) :
    finiteReal out=some (rounded d values) ∧ |rounded d values|≤(2:ℝ)^(d+1) ∧
    |rounded d values-∑i,values i|≤SumTree.budget d := by
  obtain ⟨dot,tree,zero⟩ := allowed
  have inputs : ∀j, j<2^d → finiteReal ((List.ofFn input)[0+j]!)=some (valuesAt d values (0+j)) := by
    intro j hj
    have h : j<width d := hj
    simpa [valuesAt,List.getElem!_eq_getElem?_getD,h] using finite ⟨j,h⟩
  have magnitudes : ∀j, j<2^d → |valuesAt d values (0+j)|≤2 := by
    intro j hj
    have h : j<width d := hj
    simpa [valuesAt,List.getElem!_eq_getElem?_getD,h] using small ⟨j,h⟩
  obtain ⟨value,mag,error⟩ := SumTree.accuracy (fun j => (List.ofFn input)[j]!)
    (valuesAt d values) d 0 dot bound inputs magnitudes tree
  have cap : (2:ℝ)^(d+1)≤2048 := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show d+1≤11 by exact Nat.add_le_add_right bound 1)
    norm_num at h ⊢
    exact h
  rw [ideal_eq_sum] at error
  exact ⟨SumTree.add_zero_accuracy dot out _ value (mag.trans cap) zero,mag,error⟩

/-- Universal numerical correctness refers to the actual word stored by each
completed admitted parallel execution, with no assumptions on intermediate sums. -/
theorem completed_accuracy (d : Nat) (bound : Bounds d)
    (input : Fin (width d) → Word) (values : Fin (width d) → ℝ)
    (finite : ∀i, finiteReal (input i)=some (values i)) (small : ∀i, |values i|≤2)
    (shared : List Word) (seeds : Fin (shape d).threads → Scalar.State)
    {events : List (Event (shape d).threads)} {final : State (shape d).threads}
    (run : Runs (config d bound) (program d) (initial d input shared seeds) events final)
    (halted : ∀t, (final.lanes t).halted=true)
    (source co) (valid : Dense.Admitted (shape d) (denseBounds d bound)
      (global d input) shared seeds run source co) :
    ∃ out, final.global[outputIndex d]?=some out ∧ finiteReal out=some (rounded d values) ∧
      |rounded d values-∑i,values i|≤SumTree.budget d := by
  obtain ⟨out,stored,allowed⟩ := (completed d bound input shared seeds run halted source co valid).1
  have result := output_accuracy d bound input values out finite small allowed
  exact ⟨out,stored,result.1,result.2.2⟩

end
end Ptx.Scalar.Parallel.Sum
