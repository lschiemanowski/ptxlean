import PtxTorchLean

/-! Exact closed forms for the actual TorchLean-generated scalar reverse sweep.
This does not supply or verify a PTX backward implementation. -/
namespace PtxTorchLean.AffineSquareVJP
open Spec TorchLean Proofs Proofs.Autograd
noncomputable section

abbrev scalarShape : Shape := .scalar

def inputs (x w b : ℝ) : TensorPack ℝ [scalarShape, scalarShape, scalarShape] :=
  .cons (Tensor.scalar x) (.cons (Tensor.scalar w) (.cons (Tensor.scalar b) .nil))

def graph := (PtxTorchLean.affineSquare scalarShape).toTypedGraph (PtxTorchLean.output scalarShape)

def sensitivities (x w b d : ℝ) : TensorPack ℝ [scalarShape, scalarShape, scalarShape] :=
  inputs (2*d*(x*w+b)*w) (2*d*(x*w+b)*x) (2*d*(x*w+b))

private theorem scalar_coordinate (t : Tensor ℝ scalarShape) :
    tensorToVec t (⟨0, by decide⟩ : Fin (Shape.size scalarShape)) = Tensor.item t := by
  conv_lhs => rw [← Tensor.scalar_item t]
  exact tensorToVec_scalar _ _

theorem forward_value (x w b : ℝ) :
    Tensor.item (graph.forward (inputs x w b)) = (x*w+b)^2 := by
  have h := PtxTorchLean.forward_polynomial scalarShape (Tensor.scalar x)
    (Tensor.scalar w) (Tensor.scalar b) ⟨0, by decide⟩
  simpa only [graph, inputs, tensorToVec_scalar, scalar_coordinate] using h

private theorem get_3_0 (s : Shape) (a0 a1 a2 : Tensor ℝ s) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 .nil))) (0 : Fin 3) = a0 := rfl

private theorem get_3_1 (s : Shape) (a0 a1 a2 : Tensor ℝ s) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 .nil))) (1 : Fin 3) = a1 := rfl

private theorem get_4_2 (s : Shape) (a0 a1 a2 a3 : Tensor ℝ s) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 (.cons a3 .nil)))) (2 : Fin 4) = a2 := rfl

private theorem get_4_3 (s : Shape) (a0 a1 a2 a3 : Tensor ℝ s) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 (.cons a3 .nil)))) (3 : Fin 4) = a3 := rfl

private theorem unsnoc_4 (s : Shape) (a0 a1 a2 a3 : Tensor ℝ s) :
    TorchLean.TensorPack.unsnoc (ss := [s, s, s]) (.cons a0 (.cons a1 (.cons a2 (.cons a3 .nil)))) = ((.cons a0 (.cons a1 (.cons a2 .nil))), a3) := rfl

private theorem get_5_4 (s : Shape) (a0 a1 a2 a3 a4 : Tensor ℝ s) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil))))) (4 : Fin 5) = a4 := rfl

private theorem unsnoc_5 (s : Shape) (a0 a1 a2 a3 a4 : Tensor ℝ s) :
    TorchLean.TensorPack.unsnoc (ss := [s, s, s, s]) (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil))))) = ((.cons a0 (.cons a1 (.cons a2 (.cons a3 .nil)))), a4) := rfl

private theorem unsnoc_6 (s : Shape) (a0 a1 a2 a3 a4 a5 : Tensor ℝ s) :
    TorchLean.TensorPack.unsnoc (ss := [s, s, s, s, s]) (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 .nil)))))) = ((.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil))))), a5) := rfl

-- Dependent tensor contexts need full definitional comparison while reducing
-- their shape-indexed operations; this changes elaboration, not the kernel check.
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- Reduce the actual generated reverse sweep, including both square contributions. -/
theorem generated_vjp (x w b d : ℝ) :
    graph.vjpWithSeed (inputs x w b) (Tensor.scalar d) = sensitivities x w b d := by
  simp only [graph, inputs, sensitivities, Runtime.Autograd.Torch.TypedGraph.vjpWithSeed,
    Runtime.Autograd.Torch.TypedGraphWithData.vjpWithSeed, DGraph.toTypedGraph,
    PtxTorchLean.affineSquare, DGraph.snoc, DGraph.nil, Graph.toAlgebra,
    Algebra.Graph.toData, Algebra.GraphData.backpropCtx, Algebra.GraphData.eval,
    Node.toAlgebra, TapeNodes.square, TapeNodes.add, TapeNodes.mul, Node.ofFn,
    PtxTorchLean.output, Algebra.TensorPack.single, TorchLean.TensorPack.cast,
    TorchLean.TensorPack.zero, Tensor.castShape, CtxVec.get_flattenCtx, getIdx,
    List.nil_append, List.cons_append]
  apply (Function.LeftInverse.injective (fun xs => unflattenCtx_flattenCtx xs))
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [get_3_0, get_3_1, get_4_2, get_4_3, get_5_4, unsnoc_4, unsnoc_5, unsnoc_6,
      TorchLean.TensorPack.add, TorchLean.TensorPack.snoc, flattenCtx, unflattenCtx,
      tensorToVec_addSpec, CtxVec.single, CtxVec.singleBlock, appendVec, castVec,
      Fin.append]
  all_goals simp [tensorToVec_scalar, Fin.addCases, scalarShape, Shape.size, ctxSize]
  all_goals ring_nf <;> simp

/-- Equality of the complete rank-zero forward tensor, not just its coordinate. -/
theorem forward_tensor (x w b : ℝ) :
    graph.forward (inputs x w b) = Tensor.scalar ((x*w+b)^2) := by
  rw [← forward_value x w b, Tensor.scalar_item]

/-- The actual checked upstream reverse call succeeds and returns these exact
three sensitivities together with the actual forward output. -/
theorem checked_result (x w b d : ℝ) :
    graph.vjpChecked (inputs x w b) () (Tensor.scalar d) =
      .ok (sensitivities x w b d, Tensor.scalar ((x*w+b)^2)) := by
  rw [show graph.vjpChecked (inputs x w b) () (Tensor.scalar d) =
      .ok (graph.vjpWithSeed (inputs x w b) (Tensor.scalar d),
        graph.forward (inputs x w b)) from
    PtxTorchLean.checked_success scalarShape (inputs x w b) (Tensor.scalar d)]
  rw [generated_vjp, forward_tensor]

/-- The displayed sensitivities are the derivative-adjoint applied to the seed,
using the upstream graph's analytic correctness theorem. -/
theorem sensitivities_adjoint (x w b d : ℝ) :
    flattenCtx (sensitivities x w b d) =
      (fderiv ℝ (fun v => tensorToVec (graph.forward (unflattenCtx v)))
        (flattenCtx (inputs x w b))).adjoint (tensorToVec (Tensor.scalar d)) := by
  rw [← generated_vjp]
  exact PtxTorchLean.checked_success_vjp scalarShape (inputs x w b) (Tensor.scalar d)

/-- A concrete nonunit seed tests accumulation and the x, weight, bias order. -/
theorem checked_example :
    graph.vjpChecked (inputs 2 3 1) () (Tensor.scalar 2) =
      .ok (inputs 84 56 28, Tensor.scalar 49) := by
  convert checked_result 2 3 1 2 using 1 <;> norm_num [sensitivities]

end
end PtxTorchLean.AffineSquareVJP
