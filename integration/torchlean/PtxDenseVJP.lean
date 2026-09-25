import PtxTensorContext
import NN.Proofs.Autograd.Tape.Nodes.Matrix

/-! Actual upstream matrix multiplication, vector bias and ReLU. Vectors use
column shape [n,1]; this is ordinary matrix-vector multiplication. -/
namespace PtxTorchLean.DenseVJP
open Spec TorchLean Proofs Proofs.Autograd
open TensorContext TorchLean.Tensor
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev column (n : Nat) : Shape := [n,1]
abbrev matrix (m n : Nat) : Shape := [m,n]

def inputs (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix m n))
    (b : Tensor ℝ (column m)) : TensorPack ℝ [column n,matrix m n,column m] :=
  .cons x (.cons w (.cons b .nil))

def rawGraph (m n : Nat) : Graph [column n,matrix m n,column m] [column m,column m,column m] :=
  let x : Idx ([column n,matrix m n,column m] ++ []) (column n) := ⟨⟨0,by simp⟩,rfl⟩
  let w : Idx ([column n,matrix m n,column m] ++ []) (matrix m n) := ⟨⟨1,by simp⟩,rfl⟩
  let p : Idx ([column n,matrix m n,column m] ++ [column m]) (column m) := ⟨⟨3,by simp⟩,rfl⟩
  let b : Idx ([column n,matrix m n,column m] ++ [column m]) (column m) := ⟨⟨2,by simp⟩,rfl⟩
  let a : Idx ([column n,matrix m n,column m] ++ [column m,column m]) (column m) := ⟨⟨4,by simp⟩,rfl⟩
  ((Graph.nil.snoc (TapeNodes.matmul w x)).snoc (TapeNodes.add p b)).snoc (TapeNodes.relu a)

def output (m n : Nat) : Idx ([column n,matrix m n,column m] ++ [column m,column m,column m]) (column m) :=
  ⟨⟨5,by simp⟩,rfl⟩

def graph (m n : Nat) : Runtime.Autograd.Torch.TypedGraph ℝ [column n,matrix m n,column m] (column m) where
  nodeShapes := [column m,column m,column m]
  data := (rawGraph m n).toAlgebra.toData
  output := output m n

def affine (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix m n)) (b : Tensor ℝ (column m)) :=
  addSpec (Spec.matMulSpec w x) b

def gate (a d : Tensor ℝ s) : Tensor ℝ s :=
  vecToTensor (vecOfFun fun i => ReluVJP.gate (tensorToVec a i) (tensorToVec d i))

def sensitivities (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix m n)) (b d : Tensor ℝ (column m)) :=
  let g := gate (affine x w b) d
  inputs (Spec.matMulSpec (swapAdjacentAxes w 0) g) (Spec.matMulSpec g (swapAdjacentAxes x 0)) g

private theorem get_3_0 {s0 s1 s2 : Shape} (a0 : Tensor ℝ s0) (a1 : Tensor ℝ s1) (a2 : Tensor ℝ s2) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 .nil))) (0 : Fin 3) = a0 := rfl

private theorem get_3_1 {s0 s1 s2 : Shape} (a0 : Tensor ℝ s0) (a1 : Tensor ℝ s1) (a2 : Tensor ℝ s2) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 .nil))) (1 : Fin 3) = a1 := rfl

private theorem get_3_2 {s0 s1 s2 : Shape} (a0 : Tensor ℝ s0) (a1 : Tensor ℝ s1) (a2 : Tensor ℝ s2) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 .nil))) (2 : Fin 3) = a2 := rfl

private theorem get_4_3 {s0 s1 s2 s3 : Shape} (a0 : Tensor ℝ s0) (a1 : Tensor ℝ s1) (a2 : Tensor ℝ s2) (a3 : Tensor ℝ s3) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 (.cons a3 .nil)))) (3 : Fin 4) = a3 := rfl

private theorem unsnoc_4 {s0 s1 s2 s3 : Shape} (a0 : Tensor ℝ s0) (a1 : Tensor ℝ s1) (a2 : Tensor ℝ s2) (a3 : Tensor ℝ s3) :
    TorchLean.TensorPack.unsnoc (ss := [s0, s1, s2]) (.cons a0 (.cons a1 (.cons a2 (.cons a3 .nil)))) = ((.cons a0 (.cons a1 (.cons a2 .nil))),a3) := rfl

private theorem get_5_4 {s0 s1 s2 s3 s4 : Shape} (a0 : Tensor ℝ s0) (a1 : Tensor ℝ s1) (a2 : Tensor ℝ s2) (a3 : Tensor ℝ s3) (a4 : Tensor ℝ s4) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil))))) (4 : Fin 5) = a4 := rfl

private theorem unsnoc_5 {s0 s1 s2 s3 s4 : Shape} (a0 : Tensor ℝ s0) (a1 : Tensor ℝ s1) (a2 : Tensor ℝ s2) (a3 : Tensor ℝ s3) (a4 : Tensor ℝ s4) :
    TorchLean.TensorPack.unsnoc (ss := [s0, s1, s2, s3]) (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil))))) = ((.cons a0 (.cons a1 (.cons a2 (.cons a3 .nil)))),a4) := rfl

private theorem get_6_5 {s0 s1 s2 s3 s4 s5 : Shape} (a0 : Tensor ℝ s0) (a1 : Tensor ℝ s1) (a2 : Tensor ℝ s2) (a3 : Tensor ℝ s3) (a4 : Tensor ℝ s4) (a5 : Tensor ℝ s5) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 .nil)))))) (5 : Fin 6) = a5 := rfl

private theorem unsnoc_6 {s0 s1 s2 s3 s4 s5 : Shape} (a0 : Tensor ℝ s0) (a1 : Tensor ℝ s1) (a2 : Tensor ℝ s2) (a3 : Tensor ℝ s3) (a4 : Tensor ℝ s4) (a5 : Tensor ℝ s5) :
    TorchLean.TensorPack.unsnoc (ss := [s0, s1, s2, s3, s4]) (.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 .nil)))))) = ((.cons a0 (.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil))))),a5) := rfl

private theorem get_4_2 {s0 s1 s2 s3 : Shape} (a0 : Tensor ℝ s0) (a1 : Tensor ℝ s1) (a2 : Tensor ℝ s2) (a3 : Tensor ℝ s3) :
    TorchLean.TensorPack.get (.cons a0 (.cons a1 (.cons a2 (.cons a3 .nil)))) (2 : Fin 4) = a2 := rfl

set_option backward.isDefEq.respectTransparency false in
theorem forward_value (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix m n)) (b : Tensor ℝ (column m)) :
    (graph m n).forward (inputs x w b) =
      vecToTensor (vecOfFun fun i => max (tensorToVec (affine x w b) i) 0) := by
  simp [graph,inputs,Runtime.Autograd.Torch.TypedGraph.forward,
    Runtime.Autograd.Torch.TypedGraphWithData.forward,rawGraph,Graph.toAlgebra,
    Algebra.Graph.toData,Algebra.GraphData.eval,Node.toAlgebra,
    TapeNodes.relu,TapeNodes.elemwise,TapeNodes.add,TapeNodes.matmul,Node.ofFn,
    output,CtxVec.get_flattenCtx,getIdx,TensorPack.snoc,Tensor.castShape,vecOfFun,
    get_3_0,get_3_1,get_4_2,get_4_3,get_5_4,get_6_5,affine,tensorToVec_addSpec]

set_option backward.isDefEq.respectTransparency false in
theorem generated_vjp (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix m n)) (b d : Tensor ℝ (column m)) :
    (graph m n).vjpWithSeed (inputs x w b) d = sensitivities x w b d := by
  simp only [graph,inputs,sensitivities,Runtime.Autograd.Torch.TypedGraph.vjpWithSeed,
    Runtime.Autograd.Torch.TypedGraphWithData.vjpWithSeed,rawGraph,Graph.toAlgebra,
    Algebra.Graph.toData,Algebra.GraphData.backpropCtx,Algebra.GraphData.eval,
    Node.toAlgebra,TapeNodes.relu,TapeNodes.elemwise,TapeNodes.add,TapeNodes.matmul,Node.ofFn,
    output,Algebra.TensorPack.single,TorchLean.TensorPack.cast,TorchLean.TensorPack.zero,
    Tensor.castShape,CtxVec.get_flattenCtx,getIdx,List.nil_append,List.cons_append]
  simp [get_3_0,get_3_1,get_4_2,get_4_3,get_5_4,unsnoc_4,unsnoc_5,unsnoc_6,
    unflatten_add,unflatten_single,TensorPack.single,TorchLean.TensorPack.add,TorchLean.TensorPack.snoc,TorchLean.TensorPack.zero,
    Tensor.castShape,gate,affine,ReluVJP.gate,Activation.Math.reluDerivSpec,vecOfFun,tensorToVec_addSpec]

theorem checked_result (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix m n)) (b d : Tensor ℝ (column m)) :
    (graph m n).vjpChecked (inputs x w b) () d =
      .ok (sensitivities x w b d, vecToTensor (vecOfFun fun i => max (tensorToVec (affine x w b) i) 0)) := by
  have success := Runtime.Autograd.Torch.TypedGraphWithData.vjpChecked_eq
    (graph m n) (inputs x w b) () d _ (by rfl)
  have generated := generated_vjp x w b d
  have value := forward_value x w b
  simp only [Runtime.Autograd.Torch.TypedGraph.vjpWithSeed] at generated
  simp only [Runtime.Autograd.Torch.TypedGraph.forward] at value
  exact success.trans (congrArg Except.ok (Prod.ext generated value))

set_option backward.isDefEq.respectTransparency false in
/-- Differentiability is checked at the actual intermediate affine tensor. -/
def graph_correct_at (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix m n))
    (b : Tensor ℝ (column m)) (away : ∀ i, tensorToVec (affine x w b) i ≠ 0) :
    GraphFDerivCorrectAt (rawGraph m n) (flattenCtx (inputs x w b)) := by
  unfold rawGraph
  refine ⟨⟨⟨PUnit.unit, (TapeNodes.matmulFderiv _ _).at _⟩,
    (TapeNodes.addFderiv _ _).at _⟩, TapeNodes.reluFderivAt _ _ ?_⟩
  intro i
  rw [Graph.evalVec_flattenCtx, CtxVec.get_flattenCtx]
  simpa [Graph.eval,Node.forward,Node.ofFn,TapeNodes.matmul,TapeNodes.add,
    inputs,CtxVec.get_flattenCtx,getIdx,TensorPack.snoc,Tensor.castShape,
    get_3_0,get_3_1,get_4_2,get_4_3,get_5_4,affine,tensorToVec_addSpec] using away i

/-- At nonzero affine coordinates, the generated VJP is the adjoint of the
ordinary real derivative. The execution convention at zero is a separate fact. -/
theorem sensitivities_adjoint (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix m n))
    (b d : Tensor ℝ (column m)) (away : ∀ i, tensorToVec (affine x w b) i ≠ 0) :
    flattenCtx (sensitivities x w b d) =
      (fderiv ℝ (fun v => tensorToVec ((graph m n).forward (unflattenCtx v)))
        (flattenCtx (inputs x w b))).adjoint (tensorToVec d) := by
  rw [← generated_vjp]
  apply Runtime.Autograd.Torch.TypedGraphWithData.vjpWithSeed_adjoint_fderiv
    (graph m n) (rawGraph m n).toAlgebra rfl (inputs x w b) () d
  exact (Algebra.Graph.toAlgebra_toReal (rawGraph m n) ()).symm ▸ graph_correct_at x w b away

-- Coordinate bridge adapted from TorchLean's MIT-licensed Matrix.lean
-- (pinned de3192df); upstream currently keeps this helper private.
open TapeNodes.Matmul in
theorem tensorToVec_get2 {m n : Nat} (A : Tensor ℝ [m, n]) (i : Fin m) (j :
    Fin n) :
      tensorToVec (t := A) (idxMN (m := m) (n := n) i j) = Spec.get2 A i j := by
    change
      TorchLean.Tensor.getScalar (TorchLean.Tensor.flattenSpec A)
          (idxMN (m := m) (n := n) i j) =
        Spec.get2 A i j
    rw [TorchLean.Tensor.getScalar_eq_apply]
    unfold TorchLean.Tensor.flattenSpec Spec.get2 TorchLean.Tensor.getScalar Spec.get
      TorchLean.Tensor.unstack TorchLean.Tensor.item
    rw [TorchLean.Tensor.Internal.Rep.reshape_apply_coordEquiv]
    rw [TorchLean.Tensor.Internal.Rep.unstack_apply,
      TorchLean.Tensor.Internal.Rep.unstack_apply]
    apply congrArg A
    apply TorchLean.Tensor.Internal.Coord.linearize_injective
    apply Fin.ext
    rw [TorchLean.Tensor.reshapeCoordEquiv_linearize_val]
    rw [TorchLean.Tensor.vectorCoordinate_linearize_val]
    have hlinearize :
        (TorchLean.Tensor.Internal.Coord.linearize (s := [m, n])
          (i, j, PUnit.unit)).val =
          j.val + n * i.val := by
      calc
        _ =
            (TorchLean.Tensor.Internal.Coord.linearize (s := [n])
              (j, PUnit.unit)).val +
              TorchLean.Tensor.Internal.Shape.size [n] * i.val :=
          TorchLean.Tensor.Internal.Coord.linearize_cons_val (s := [n]) i (j, PUnit.unit)
        _ = j.val + n * i.val := by
          rw [TorchLean.Tensor.vectorCoordinate_linearize_val]
          simp
    rw [hlinearize]
    simp [idxMN, finProdFinEquiv_apply_val]


/-- The tensor-level affine expression is exactly matrix-vector multiplication
plus the row's bias, including the empty inner dimension. -/
theorem affine_coordinate (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix m n))
    (b : Tensor ℝ (column m)) (row : Fin m) :
    Spec.get2 (affine x w b) row 0 =
      (∑ j : Fin n, Spec.get2 w row j * Spec.get2 x j 0) + Spec.get2 b row 0 := by
  simp [affine,addSpec,Spec.get2_mat_mul_spec]

theorem gate_coordinate (a d : Tensor ℝ (column m)) (row : Fin m) :
    Spec.get2 (gate a d) row 0 = ReluVJP.gate (Spec.get2 a row 0) (Spec.get2 d row 0) := by
  rw [← tensorToVec_get2,gate]
  simp [vecOfFun,tensorToVec_get2]

theorem forward_coordinate (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix m n))
    (b : Tensor ℝ (column m)) (row : Fin m) :
    Spec.get2 ((graph m n).forward (inputs x w b)) row 0 =
      max ((∑ j : Fin n, Spec.get2 w row j * Spec.get2 x j 0) + Spec.get2 b row 0) 0 := by
  rw [forward_value,← tensorToVec_get2]
  simp [vecOfFun,tensorToVec_get2,affine_coordinate]

/-- Coordinate form of all three tensors in the actual generated backward. -/
theorem backward_coordinates (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix m n))
    (b d : Tensor ℝ (column m)) :
    let result := (graph m n).vjpWithSeed (inputs x w b) d
    let g := gate (affine x w b) d
    (∀ j : Fin n, Spec.get2 (TorchLean.TensorPack.get result 0) j 0 =
      ∑ i : Fin m, Spec.get2 w i j * Spec.get2 g i 0) ∧
    (∀ i : Fin m, ∀ j : Fin n, Spec.get2 (TorchLean.TensorPack.get result 1) i j =
      Spec.get2 g i 0 * Spec.get2 x j 0) ∧
    (∀ i : Fin m, Spec.get2 (TorchLean.TensorPack.get result 2) i 0 = Spec.get2 g i 0) := by
  dsimp only
  rw [generated_vjp]
  simp [sensitivities,inputs,get_3_0,get_3_1,get_3_2,Spec.get2_mat_mul_spec,Spec.get2_matrix_transpose_spec]

/-- The real graph retains the ordinary empty-sum convention. -/
theorem empty_input_forward (x : Tensor ℝ (column 0)) (w : Tensor ℝ (matrix m 0))
    (b : Tensor ℝ (column m)) (row : Fin m) :
    Spec.get2 ((graph m 0).forward (inputs x w b)) row 0 = max (Spec.get2 b row 0) 0 := by
  simp [forward_coordinate]

/-- With no outputs, every input sensitivity is zero. -/
theorem empty_output_dx (x : Tensor ℝ (column n)) (w : Tensor ℝ (matrix 0 n))
    (b d : Tensor ℝ (column 0)) (j : Fin n) :
    Spec.get2 (TorchLean.TensorPack.get ((graph 0 n).vjpWithSeed (inputs x w b) d) 0) j 0 = 0 := by
  simpa using (backward_coordinates x w b d).1 j

/-- A convention for execution at the kink, without claiming differentiability. -/
theorem gate_at_zero (a d : Tensor ℝ (column m)) (row : Fin m) (zero : Spec.get2 a row 0 = 0) :
    Spec.get2 (gate a d) row 0 = 0 := by
  simp [gate_coordinate,ReluVJP.gate,zero]

end
end PtxTorchLean.DenseVJP

