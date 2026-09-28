import PtxSoftmaxParallel

/-! The backward reference is TorchLean's actual softmax derivative. The forward
report derives a finite magnitude bound for the words supplied to backward. -/
namespace PtxTorchLean.Softmax
open TorchLean Proofs.Autograd
open scoped BigOperators _root_.Autograd
noncomputable section

def rowBackward (values incoming : Fin n → ℝ) (i : Fin n) : ℝ :=
  Tensor.getScalar (Activation.softmaxBackwardSpec 0 (Tensor.ofFn values) (Tensor.ofFn incoming)) i

theorem rowBackward_formula (values incoming : Fin n → ℝ) (i : Fin n) :
    rowBackward values incoming i = rowForward values i *
      (incoming i-∑j,rowForward values j*incoming j) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    simpa [rowBackward,rowForward,backward,forward] using
      backward_formula (Tensor.ofFn values) (Tensor.ofFn incoming) i

/-- The coordinate formula is the actual vector-Jacobian product of the pinned
real tensor operation, not the derivative of floating-point rounding. -/
theorem rowBackward_is_vjp (values incoming : Vec n) (positive : 0<n) (i : Fin n) :
    rowBackward values.ofLp incoming.ofLp i =
      (VJP[fun v : Vec n => getScalarE
        (Activation.softmaxSpec (α:=ℝ) (s:=[n]) 0 (ofFnE v)), values] incoming).ofLp i := by
  cases n with
  | zero => omega
  | succ n =>
    have h := backward_is_vjp (ofFnE values) (ofFnE incoming)
    simp only [getScalarE_ofFnE] at h
    have eq := congrArg (fun v : Vec (n+1) => v.ofLp i) h
    simpa only [getScalarE_ofLp,ofFnE,EuclideanSpace.equiv,PiLp.coe_continuousLinearEquiv,rowBackward] using eq

end
end PtxTorchLean.Softmax

namespace PtxTorchLean.SoftmaxBackward
open Ptx Ptx.Binary32 Ptx.Scalar Ptx.Scalar.Parallel
open SoftmaxPipeline
noncomputable section

/-- Derive the actual finite forward values, magnitude four and the inherited
error allowance from original scores and the forward run. -/
theorem forward_report (d : Nat) (bound : d≤10)
    (input : Fin (Sum.width d) → Word) (values : Fin (Sum.width d) → ℝ)
    (finite : ∀i, finiteReal (input i)=some (values i))
    (small : ∀i, |values i|≤(2:ℝ)^(124:ℤ))
    (guard : SoftmaxPipeline.AccuracyGuard d values)
    (run : Scalar.SoftmaxParallel.Run d input forward) :
    ∃ (m : ℝ) (u : Fin (Sum.width d) → ℝ),
      finiteReal (Scalar.SoftmaxPipeline.maximumWord d input)=some m ∧
      ∀i, finiteReal forward[i.val]! =some (resultValue d u i) ∧
        |resultValue d u i|≤4 ∧
        |resultValue d u i-Softmax.rowForward values i|≤coordinateAllowance d values m u i := by
  obtain ⟨len,m,u,exponentials,denominator,mvalue,upper,attained,expStages,sumStages,normStages,
    expValues,denValue,den,outputs,total⟩ :=
    PtxTorchLean.SoftmaxParallel.correct d bound input values finite small guard run
  obtain ⟨v,vvalue,vmag,_⟩ := Binary32.SoftmaxForward.exponentials input exponentials
    (Scalar.SoftmaxPipeline.maximumWord d input) values m finite mvalue upper attained small expStages
  have mag : ∀i, |u i|≤2 := by
    intro i
    have eq := Option.some.inj ((vvalue i).symm.trans (expValues i))
    simpa [eq] using vmag i
  refine ⟨m,u,mvalue,?_⟩
  intro i
  have checked := Binary32.Normalize.correct (exponentials i) denominator forward[i.val]!
    (u i) (Sum.rounded d u) (expValues i) denValue (mag i) den (normStages i)
  obtain ⟨word,stored,wordValue,error⟩ := outputs i
  exact ⟨checked.1,checked.2.2.2,error⟩

end
end PtxTorchLean.SoftmaxBackward
