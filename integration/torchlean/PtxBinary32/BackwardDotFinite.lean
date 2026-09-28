import PtxBinary32.BackwardDot

/-! Finite row interfaces for the backward dot-product arithmetic. -/
namespace Ptx.Binary32.BackwardDot
open scoped BigOperators
noncomputable section

def valuesAt (d : Nat) (values : Fin (2^d) → ℝ) (j : Nat) : ℝ := (List.ofFn values)[j]!
def vector_rounded (d : Nat) (gv pv : Fin (2^d) → ℝ) : ℝ :=
  rounded (valuesAt d gv) (valuesAt d pv) d 0
def vector_budget (d : Nat) (gv pv : Fin (2^d) → ℝ) : ℝ :=
  budget (valuesAt d gv) (valuesAt d pv) d 0

theorem ideal_eq_sum (d : Nat) (gv pv : Fin (2^d) → ℝ) :
    ideal (valuesAt d gv) (valuesAt d pv) d 0=∑i,pv i*gv i := by
  rw [ideal_sum]
  have same : (List.range (2^d)).map
      (fun j => valuesAt d gv (0+j)*valuesAt d pv (0+j)) = List.ofFn (fun i => pv i*gv i) := by
    apply List.ext_getElem (by simp)
    intro j hj hj'
    have h : j<2^d := by simpa only [List.length_ofFn] using hj'
    simp [valuesAt,List.getElem!_eq_getElem?_getD,h,mul_comm]
  rw [same,List.sum_ofFn]

/-- The dense output includes its final +0 instruction. Saved forward weights
are the actual finite values, and their error versus ideal weights is composed
separately. -/
theorem output_accuracy (d : Nat) (bound : d≤10)
    (g p : Fin (2^d) → Word) (gv pv : Fin (2^d) → ℝ) (dot out : Word)
    (finiteG : ∀i,finiteReal (g i)=some (gv i))
    (finiteP : ∀i,finiteReal (p i)=some (pv i))
    (smallG : ∀i,|gv i|≤(2:ℝ)^60) (smallP : ∀i,|pv i|≤4)
    (tree : Reduction.Eval (Reduction.balanced d 0
      (fun j => ((List.ofFn g)[j]!, (List.ofFn p)[j]!))) dot)
    (zero : Results .add dot 0 out) :
    finiteReal out=some (vector_rounded d gv pv) ∧
    |vector_rounded d gv pv|≤(2:ℝ)^72 ∧
    |vector_rounded d gv pv-∑i,pv i*gv i|≤vector_budget d gv pv := by
  have fg : ∀j,j<2^d → finiteReal ((List.ofFn g)[0+j]!)=some (valuesAt d gv (0+j)) := by
    intro j hj
    simpa [valuesAt,List.getElem!_eq_getElem?_getD,hj] using finiteG ⟨j,hj⟩
  have fp : ∀j,j<2^d → finiteReal ((List.ofFn p)[0+j]!)=some (valuesAt d pv (0+j)) := by
    intro j hj
    simpa [valuesAt,List.getElem!_eq_getElem?_getD,hj] using finiteP ⟨j,hj⟩
  have sg : ∀j,j<2^d → |valuesAt d gv (0+j)|≤(2:ℝ)^60 := by
    intro j hj
    simpa [valuesAt,List.getElem!_eq_getElem?_getD,hj] using smallG ⟨j,hj⟩
  have sp : ∀j,j<2^d → |valuesAt d pv (0+j)|≤4 := by
    intro j hj
    simpa [valuesAt,List.getElem!_eq_getElem?_getD,hj] using smallP ⟨j,hj⟩
  obtain ⟨value,mag,error⟩ := accuracy (fun j => (List.ofFn g)[j]!) (fun j => (List.ofFn p)[j]!)
    (valuesAt d gv) (valuesAt d pv) d 0 dot bound fg fp sg sp tree
  have cap : (2:ℝ)^(d+62)≤(2:ℝ)^72 := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [ideal_eq_sum] at error
  exact ⟨add_zero_accuracy dot out _ value (mag.trans cap) zero,mag.trans cap,error⟩

end
end Ptx.Binary32.BackwardDot
