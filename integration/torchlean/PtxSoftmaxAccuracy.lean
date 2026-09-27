import PtxBinary32.SoftmaxError
import NN.Proofs.Autograd.FDeriv.SoftmaxSpec

/-! Stable-softmax numerical contracts against the pinned TorchLean specification.
No PTX instruction, fetched program or launch correspondence is asserted here. -/
namespace PtxTorchLean.Softmax
open TorchLean TorchLean.Tensor Proofs.Autograd
open scoped BigOperators _root_.Autograd
open Ptx.Numerics.Softmax
noncomputable section

/-- Exact shifted exponentials; this definition is the actual TorchLean tensor. -/
def weights (x : Tensor ℝ [n+1]) : Fin (n+1) → ℝ :=
  Tensor.getScalar (Activation.maxShiftedExpVecSpec x)

def forward (x : Tensor ℝ [n+1]) : Fin (n+1) → ℝ :=
  Tensor.getScalar (Activation.softmaxVecSpec x)

def backward (x d : Tensor ℝ [n+1]) : Fin (n+1) → ℝ :=
  Tensor.getScalar (Activation.softmaxBackwardSpec 0 x d)

theorem weights_bounds (x : Tensor ℝ [n+1]) :
    (∀ i, 0 < weights x i ∧ weights x i ≤ 1) ∧
      1 ≤ ∑ i, weights x i ∧ (∑ i, weights x i) ≤ n+1 := by
  refine ⟨fun i => ⟨Proofs.softmax_shift_exp_pos x i, Proofs.softmax_shift_exp_le_one x i⟩, ?_⟩
  have h := Proofs.softmax_shift_denom_bounds x
  rw [Spec.sum_spec_vec] at h
  simpa [weights] using h

theorem forward_formula (x : Tensor ℝ [n+1]) (i : Fin (n+1)) :
    forward x i = weights x i / (∑ j, weights x j) := by
  simp [forward, weights, Activation.softmaxVecSpec, Tensor.divSpec, Spec.replicate,
    Tensor.getScalar_map2Spec, Spec.sum_spec_vec]

theorem forward_error (x : Tensor ℝ [n+1])
    (h : Stages (weights x) approximate sum reciprocal output delta sigma rho tau)
    (small : denominatorBudget delta sigma < 1) (i : Fin (n+1)) :
    |output i-forward x i| ≤
      coordinateBudget (delta i) (denominatorBudget delta sigma) rho (tau i) := by
  rw [forward_formula]
  exact coordinate_error h (fun j => (weights_bounds x).1 j |>.1.le)
    (fun j => (weights_bounds x).1 j |>.2) (weights_bounds x).2.1 small i

theorem computed_denominator_positive (x : Tensor ℝ [n+1])
    (h : Stages (weights x) approximate sum reciprocal output delta sigma rho tau)
    (small : denominatorBudget delta sigma < 1) :
    1-denominatorBudget delta sigma ≤ sum ∧ 0 < sum :=
  denominator_positive h (weights_bounds x).2.1 small

theorem computed_normalization_error (x : Tensor ℝ [n+1])
    (h : Stages (weights x) approximate sum reciprocal output delta sigma rho tau)
    (small : denominatorBudget delta sigma < 1) :
    |(∑ i, output i)-1| ≤ ∑ i, coordinateBudget (delta i) (denominatorBudget delta sigma) rho (tau i) :=
  normalization_error h (fun j => (weights_bounds x).1 j |>.1.le)
    (fun j => (weights_bounds x).1 j |>.2) (weights_bounds x).2.1 small

theorem backward_formula (x d : Tensor ℝ [n+1]) (i : Fin (n+1)) :
    backward x d i = forward x i * (Tensor.getScalar d i - ∑ j, forward x j * Tensor.getScalar d j) := by
  have h := congrFun (congrArg (fun v => fun j => v j)
    (Proofs.Autograd.getScalarE_softmaxBackwardSpec x d)) i
  simpa [backward, forward, Proofs.Autograd.softmaxJvp, Proofs.Autograd.dotCLM_apply,
    ← Proofs.Autograd.getScalarE_softmaxVecSpec] using h

/-- The exact backward target is the adjoint of the true derivative, not merely
an agreed algebraic rule or a derivative of floating-point rounding. -/
theorem backward_is_vjp (x d : Tensor ℝ [n+1]) :
    getScalarE (Activation.softmaxBackwardSpec (α := ℝ) (s := [n+1]) 0 x d) =
      VJP[fun xV : Proofs.Autograd.Vec (n+1) =>
        getScalarE (Activation.softmaxSpec (α := ℝ) (s := [n+1]) 0 (ofFnE xV)),
        getScalarE x] (getScalarE d) :=
  Proofs.Autograd.softmaxBackwardSpec_eq_vjp x d

theorem backward_error (x d : Tensor ℝ [n+1])
    (h : BackwardStages (forward x) pHat (Tensor.getScalar d) dHat dot
      difference gradient epsilon eta sigma subError mulError) (i : Fin (n+1)) :
    |gradient i-backward x d i| ≤
      backwardBudget pHat (Tensor.getScalar d) (forward x) epsilon eta subError mulError sigma i := by
  rw [backward_formula]
  exact backward_coordinate_error h i

/-- Reuse the actual approximate forward output in backward; its error is
proved above, rather than required again as a caller-supplied hypothesis. -/
theorem backward_error_of_forward (x d : Tensor ℝ [n+1])
    (h : Stages (weights x) approximate sum reciprocal output delta sigma rho tau)
    (small : denominatorBudget delta sigma < 1)
    (dHat difference gradient eta subError mulError : Fin (n+1) → ℝ)
    (dot dotError : ℝ)
    (incoming : ∀ i, |dHat i-Tensor.getScalar d i| ≤ eta i)
    (reduction : |dot-∑ i, output i*dHat i| ≤ dotError)
    (subtraction : ∀ i, |difference i-(dHat i-dot)| ≤ subError i)
    (multiplication : ∀ i, |gradient i-output i*difference i| ≤ mulError i)
    (i : Fin (n+1)) :
    |gradient i-backward x d i| ≤
      backwardBudget output (Tensor.getScalar d) (forward x)
        (fun j => coordinateBudget (delta j) (denominatorBudget delta sigma) rho (tau j))
        eta subError mulError dotError i := by
  exact backward_error x d ⟨forward_error x h small, incoming, reduction,
    subtraction, multiplication⟩ i

end
end PtxTorchLean.Softmax
