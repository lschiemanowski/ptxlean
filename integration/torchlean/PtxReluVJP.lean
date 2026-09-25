import PtxTorchLean

/-! Exact closed forms for the actual TorchLean-generated scalar reverse sweep.
The zero-gradient convention is separate from differentiability away from zero. -/
namespace PtxTorchLean.ReluVJP
open Spec TorchLean Proofs Proofs.Autograd
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

abbrev scalarShape : Shape := .scalar

def inputs (x w b : ℝ) : TensorPack ℝ [scalarShape, scalarShape, scalarShape] :=
  .cons (Tensor.scalar x) (.cons (Tensor.scalar w) (.cons (Tensor.scalar b) .nil))

def rawGraph : Graph [scalarShape, scalarShape, scalarShape] [scalarShape, scalarShape, scalarShape] :=
  let x : Idx ([scalarShape, scalarShape, scalarShape] ++ []) scalarShape := ⟨⟨0, by simp⟩, rfl⟩
  let w : Idx ([scalarShape, scalarShape, scalarShape] ++ []) scalarShape := ⟨⟨1, by simp⟩, rfl⟩
  let p : Idx ([scalarShape, scalarShape, scalarShape] ++ [scalarShape]) scalarShape := ⟨⟨3, by simp⟩, rfl⟩
  let b : Idx ([scalarShape, scalarShape, scalarShape] ++ [scalarShape]) scalarShape := ⟨⟨2, by simp⟩, rfl⟩
  let a : Idx ([scalarShape, scalarShape, scalarShape] ++ [scalarShape, scalarShape]) scalarShape := ⟨⟨4, by simp⟩, rfl⟩
  ((Graph.nil.snoc (TapeNodes.mul w x)).snoc (TapeNodes.add p b)).snoc (TapeNodes.relu a)

def graph : Runtime.Autograd.Torch.TypedGraph ℝ [scalarShape, scalarShape, scalarShape] scalarShape where
  nodeShapes := [scalarShape, scalarShape, scalarShape]
  data := rawGraph.toAlgebra.toData
  output := PtxTorchLean.output scalarShape

def gate (a d : ℝ) : ℝ := if 0 < a then d else 0

def sensitivities (x w b d : ℝ) : TensorPack ℝ [scalarShape, scalarShape, scalarShape] :=
  inputs (gate (w*x+b) d*w) (gate (w*x+b) d*x) (gate (w*x+b) d)

private theorem scalar_coordinate (t : Tensor ℝ scalarShape) :
    tensorToVec t (⟨0, by decide⟩ : Fin (Shape.size scalarShape)) = Tensor.item t := by
  conv_lhs => rw [← Tensor.scalar_item t]
  exact tensorToVec_scalar _ _

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

private theorem get_6_5 (s : Shape) (a0 a1 a2 a3 a4 a5 : Tensor ℝ s) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 .nil)))))) (5 : Fin 6) = a5 := rfl

-- Dependent tensor contexts need full definitional comparison while reducing
-- their shape-indexed operations; this changes elaboration, not the kernel check.
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The actual generated reverse sweep uses zero at the kink. -/
theorem generated_vjp (x w b d : ℝ) :
    graph.vjpWithSeed (inputs x w b) (Tensor.scalar d) = sensitivities x w b d := by
  simp only [graph, inputs, sensitivities, Runtime.Autograd.Torch.TypedGraph.vjpWithSeed,
    Runtime.Autograd.Torch.TypedGraphWithData.vjpWithSeed,
    rawGraph, Graph.toAlgebra,
    Algebra.Graph.toData, Algebra.GraphData.backpropCtx, Algebra.GraphData.eval,
    Node.toAlgebra, TapeNodes.relu, TapeNodes.elemwise, TapeNodes.add, TapeNodes.mul, Node.ofFn,
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
  all_goals simp [gate, Activation.Math.reluDerivSpec]


theorem forward_value (x w b : ℝ) :
    Tensor.item (graph.forward (inputs x w b)) = max (w*x+b) 0 := by
  have h : tensorToVec (graph.forward (inputs x w b)) (⟨0, by decide⟩ : Fin 1) = max (w*x+b) 0 := by
    simp [graph, inputs, Runtime.Autograd.Torch.TypedGraph.forward,
      Runtime.Autograd.Torch.TypedGraphWithData.forward, rawGraph, Graph.toAlgebra,
      Algebra.Graph.toData, Algebra.GraphData.eval, Node.toAlgebra,
      TapeNodes.relu, TapeNodes.elemwise, TapeNodes.add, TapeNodes.mul, Node.ofFn,
      PtxTorchLean.output, CtxVec.get_flattenCtx, getIdx, TensorPack.snoc,
      Tensor.castShape, vecOfFun, get_3_0, get_3_1, get_4_2, get_4_3, get_5_4, get_6_5,
      tensorToVec_scalar]
  exact (scalar_coordinate (graph.forward (inputs x w b))).symm.trans h

theorem checked_result (x w b d : ℝ) :
    graph.vjpChecked (inputs x w b) () (Tensor.scalar d) =
      .ok (sensitivities x w b d, Tensor.scalar (max (w*x+b) 0)) := by
  have success := Runtime.Autograd.Torch.TypedGraphWithData.vjpChecked_eq
    graph (inputs x w b) () (Tensor.scalar d) _ (by rfl)
  have generated := generated_vjp x w b d
  have value : graph.forward (inputs x w b) = Tensor.scalar (max (w*x+b) 0) :=
    (Tensor.scalar_item _).symm.trans (congrArg Tensor.scalar (forward_value x w b))
  simp only [Runtime.Autograd.Torch.TypedGraph.vjpWithSeed] at generated
  simp only [Runtime.Autograd.Torch.TypedGraph.forward] at value
  exact success.trans (congrArg Except.ok (Prod.ext generated value))

-- Permit definitional unfolding of the shape-indexed graph while elaborating this proof.
-- This Meta elaborator option does not alter Lean kernel checking.
set_option backward.isDefEq.respectTransparency false in
/-- Every primitive is differentiable at its actual forward input away from the kink. -/
def graph_correct_at (x w b : ℝ) (away : w*x+b ≠ 0) :
    GraphFDerivCorrectAt rawGraph (flattenCtx (inputs x w b)) := by
  unfold rawGraph
  refine ⟨⟨⟨PUnit.unit, (TapeNodes.mulFderiv _ _).at _⟩,
    (TapeNodes.addFderiv _ _).at _⟩, TapeNodes.reluFderivAt _ _ ?_⟩
  intro i
  have hi : i = ⟨0, by decide⟩ := Fin.eq_zero i
  subst i
  simp only [Graph.evalVec, TapeNodes.add, TapeNodes.mul, Node.forwardVec_ofFn]
  simpa [snocCtx, CtxVec.get, CtxVec.getBlock, scalarShape, Shape.size, ctxSize,
    inputs, flattenCtx, vecOfFun, tensorToVec_scalar, castCtxVec, castVec,
    appendVec, Fin.append, Fin.addCases, EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply] using away

/-- The generated backward is the ordinary mathematical derivative only away from zero. -/
theorem sensitivities_adjoint (x w b d : ℝ) (away : w*x+b ≠ 0) :
    flattenCtx (sensitivities x w b d) =
      (fderiv ℝ (fun v => tensorToVec (graph.forward (unflattenCtx v)))
        (flattenCtx (inputs x w b))).adjoint (tensorToVec (Tensor.scalar d)) := by
  rw [← generated_vjp]
  apply Runtime.Autograd.Torch.TypedGraphWithData.vjpWithSeed_adjoint_fderiv
    graph rawGraph.toAlgebra rfl (inputs x w b) () (Tensor.scalar d)
  exact (Algebra.Graph.toAlgebra_toReal rawGraph ()).symm ▸ graph_correct_at x w b away

end
end PtxTorchLean.ReluVJP
