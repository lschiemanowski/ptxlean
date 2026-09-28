import PtxBinary32.SoftmaxBackwardDot
import PtxBinary32.BackwardDotFinite

/-! Numerical interpretation of the actual backward dot's permitted stored
results. The operand order and tree rounding order remain explicit; only the
ideal real-valued target uses commutativity of multiplication. -/
namespace Ptx.Scalar.Parallel.SoftmaxBackwardDot
open Ptx.Binary32
open scoped BigOperators
noncomputable section

/-- Accuracy is derived from the supplied finite operands. Intermediate
finiteness, including the stored final +0 result, is a conclusion. -/
theorem output_accuracy (d : Nat) (bound : Sum.Bounds d)
    (p g : Fin (Sum.width d) → Word) (pv gv : Fin (Sum.width d) → ℝ) (out : Word)
    (finiteP : ∀i,finiteReal (p i)=some (pv i))
    (finiteG : ∀i,finiteReal (g i)=some (gv i))
    (smallP : ∀i,|pv i|≤4) (smallG : ∀i,|gv i|≤(2:ℝ)^60)
    (allowed : Output d p g out) :
    finiteReal out=some (BackwardDot.vector_rounded d gv pv) ∧
    |BackwardDot.vector_rounded d gv pv|≤(2:ℝ)^72 ∧
    |BackwardDot.vector_rounded d gv pv-∑i,pv i*gv i|≤BackwardDot.vector_budget d gv pv := by
  obtain ⟨dot,tree,zero⟩ := allowed
  exact BackwardDot.output_accuracy d bound g p gv pv dot out finiteG finiteP smallG smallP tree zero

/-- Every completed admitted launch stores an accurate finite dot result while
preserving both original input arrays and the bias exactly. -/
theorem launch_accuracy (d : Nat) (bound : Sum.Bounds d)
    (p g : Fin (Sum.width d) → Word) (pv gv : Fin (Sum.width d) → ℝ)
    (finiteP : ∀i,finiteReal (p i)=some (pv i))
    (finiteG : ∀i,finiteReal (g i)=some (gv i))
    (smallP : ∀i,|pv i|≤4) (smallG : ∀i,|gv i|≤(2:ℝ)^60)
    (run : Launch d p g after) :
    ∃out, after=(global d p g).set (outputIndex d) out ∧
      finiteReal out=some (BackwardDot.vector_rounded d gv pv) ∧
      |BackwardDot.vector_rounded d gv pv|≤(2:ℝ)^72 ∧
      |BackwardDot.vector_rounded d gv pv-∑i,pv i*gv i|≤BackwardDot.vector_budget d gv pv := by
  obtain ⟨out,stored,allowed⟩ := launch_correct d p g run
  exact ⟨out,stored,output_accuracy d bound p g pv gv out finiteP finiteG smallP smallG allowed⟩

end
end Ptx.Scalar.Parallel.SoftmaxBackwardDot
