import PtxBinary32.SoftmaxForwardAccuracy
import PtxSoftmaxAccuracy

/-! Identify the real target of the encoded softmax composition with the pinned
TorchLean stable-softmax tensor specification. -/
namespace PtxTorchLean.Softmax
open TorchLean
open scoped BigOperators
noncomputable section

/-- Apply the pinned tensor specification to the original row of real scores. -/
def rowForward (values : Fin n → ℝ) (i : Fin n) : ℝ :=
  Tensor.getScalar (Activation.softmaxVecSpec (Tensor.ofFn values)) i

/-- Any attained upper bound is the maximum used by TorchLean's own stable
softmax. There is no separate or caller-supplied network specification. -/
theorem rowForward_formula (values : Fin n → ℝ) (m : ℝ)
    (upper : ∀i, values i≤m) (attained : ∃i, values i=m) (i : Fin n) :
    rowForward values i = Ptx.Binary32.SoftmaxForward.exact values m i /
      (∑j,Ptx.Binary32.SoftmaxForward.exact values m j) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let x := Tensor.ofFn values
    have mx : Tensor.item (Activation.maxVecSpec x)=m := by
      apply le_antisymm
      · obtain ⟨j,hj⟩ := Proofs.exists_getScalar_eq_maxVecSpec x
        rw [← hj]
        simpa [x] using upper j
      · obtain ⟨j,hj⟩ := attained
        have h := Proofs.getScalar_le_maxVecSpec x j
        simpa [x,hj] using h
    have weights : ∀j, weights x j=Ptx.Binary32.SoftmaxForward.exact values m j := by
      intro j
      rw [Softmax.weights,Proofs.getScalar_maxShiftedExpVecSpec,mx]
      simp [x,Ptx.Binary32.SoftmaxForward.exact]
    have formula := forward_formula x i
    simp only [weights] at formula
    exact formula

/-- Transport a proved encoded-result error to the actual TorchLean result. -/
theorem rowForward_error (values : Fin n → ℝ) (m y error : ℝ)
    (upper : ∀i, values i≤m) (attained : ∃i, values i=m) (i : Fin n)
    (proved : |y-Ptx.Binary32.SoftmaxForward.exact values m i /
      (∑j,Ptx.Binary32.SoftmaxForward.exact values m j)|≤error) :
    |y-rowForward values i|≤error := by
  rwa [rowForward_formula values m upper attained i]

end
end PtxTorchLean.Softmax
