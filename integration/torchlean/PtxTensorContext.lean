import PtxVectorVJP

/-! Context identities used to reduce actual heterogeneous upstream reverse sweeps
without exposing flattened index arithmetic in every example. -/
namespace PtxTorchLean.TensorContext
open Spec TorchLean Proofs Proofs.Autograd
noncomputable section

/-- Sparse tensor contexts and sparse vector contexts describe the same seed. -/
theorem single_flatten {Γ : List Shape} (idx : Idx Γ s) (v : Tensor ℝ s) :
    CtxVec.single idx (tensorToVec v) = flattenCtx (TensorPack.single idx v) := by
  apply ext_inner_left ℝ
  intro x
  have hx : x = flattenCtx (unflattenCtx x) := (flattenCtx_unflattenCtx x).symm
  rw [hx,CtxVec.inner_get_single,← dotList_eq_inner_flattenCtx,TensorPack.dotList_single,
    dot_eq_inner_tensorToVec,CtxVec.get_flattenCtx]

@[simp] theorem unflatten_single {Γ : List Shape} (idx : Idx Γ s) (v : Vec s.size) :
    unflattenCtx (CtxVec.single idx v) = TensorPack.single idx (vecToTensor v) := by
  have h := single_flatten idx (vecToTensor v)
  simp only [tensorToVec_vecToTensor] at h
  rw [h,unflattenCtx_flattenCtx]

@[simp] theorem unflatten_add {Γ : List Shape} (a b : CtxVec Γ) :
    unflattenCtx (a+b) = TorchLean.TensorPack.add (unflattenCtx a) (unflattenCtx b) := by
  apply (Function.LeftInverse.injective (fun xs => unflattenCtx_flattenCtx xs))
  simp [flattenCtx_add]

end
end PtxTorchLean.TensorContext
