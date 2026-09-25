import PtxVectorKernel
import PtxVectorVJP
import PtxBinary32.DotError

/-! Accuracy for all completed reference-neuron executions. Range and branch
conditions are calculated from initial inputs and explicit rounded expressions. -/
namespace PtxTorchLean.VectorKernel
open Ptx Ptx.Scalar Ptx.Scalar.Sequential Ptx.SequentialStorage
open Binary32 (finiteReal)
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open Binary32.BackwardError (StageRange stageBudget roundedProduct)
open Spec TorchLean Proofs Proofs.Autograd TorchLean.Floats
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The initialized constant +1 has its actual binary32 interpretation. -/
theorem one_real : finiteReal (0x3f800000 : Word) = some 1 := by
  rw [Binary32.finiteReal_some _ (by decide)]
  change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 127 0)) = some 1
  rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
  norm_num [FloatFormat.binary32,Model.pow2,FloatLib.Floats.Formats.Flocq.bpow,
    FloatLib.Numerics.binaryRadix,FloatLib.Numerics.Radix.toReal]

structure Inputs {s : Shape} (d : Buffer s.size) where
  entries : Fin s.size → Binary32.DotError.Input
  leftWords : ∀ j, (entries j).left = d (weight j)
  rightWords : ∀ j, (entries j).right = d (input j)
  one : d (slot 1) = 0x3f800000
  zero : d (slot 7) = 0
  bh : ℝ
  b : ℝ
  eb : ℝ
  bReal : finiteReal (d (slot 2)) = some bh
  bError : |bh-b| ≤ eb
  safe : Binary32.DotError.Safe (List.ofFn entries) 0
  multiplyRange : |Binary32.DotError.rounded (List.ofFn entries) 0 * 1| ≤ Binary32.Bounds.maxFinite
  additionRange : |Binary32.DotError.rounded (List.ofFn entries) 0 * 1| +
    Floats.eps32 (Binary32.DotError.rounded (List.ofFn entries) 0 * 1) + |bh| ≤ Binary32.Bounds.maxFinite

variable {s : Shape} {d out : Buffer s.size}

noncomputable def Inputs.x (i : Inputs (s := s) d) : Tensor ℝ s :=
  vecToTensor (vecOfFun fun j => (i.entries j).r)
noncomputable def Inputs.w (i : Inputs (s := s) d) : Tensor ℝ s :=
  vecToTensor (vecOfFun fun j => (i.entries j).l)
noncomputable def Inputs.dot (i : Inputs d) : ℝ := Binary32.DotError.rounded (List.ofFn i.entries) 0
noncomputable def Inputs.dotBudget (i : Inputs d) : ℝ := Binary32.DotError.budget (List.ofFn i.entries) 0
noncomputable def Inputs.idealDot (i : Inputs d) : ℝ := ∑ j, (i.entries j).l * (i.entries j).r
noncomputable def Inputs.affine (i : Inputs d) : ℝ := Binary32.SquareError.roundedAffine i.dot 1 i.bh
noncomputable def Inputs.budget (i : Inputs d) : ℝ :=
  Binary32.Error.affineBudget i.dot 1 i.bh i.idealDot 1 i.dotBudget 0 i.eb

@[simp] theorem Inputs.graph_affine (i : Inputs d) : VectorVJP.affine i.x i.w i.b = i.idealDot+i.b := by
  simp [VectorVJP.affine,Inputs.x,Inputs.w,Inputs.idealDot,vecOfFun]

theorem Inputs.dot_facts (i : Inputs d) (fold : Dot.Fold (pairs d) 0 z) :
    finiteReal z = some i.dot ∧ |i.dot-i.idealDot| ≤ i.dotBudget := by
  have hw : Binary32.DotError.words (List.ofFn i.entries) = pairs d := by
    simp [Binary32.DotError.words,pairs,List.map_ofFn,Function.comp_def,i.leftWords,i.rightWords]
  obtain ⟨value,error⟩ := Binary32.DotError.fold_accuracy (List.ofFn i.entries) 0 z 0 0 0
    Binary32.SquareError.zero_real (by simp) i.safe (hw ▸ fold)
  exact ⟨value,by simpa [Inputs.dot,Inputs.dotBudget,Inputs.idealDot,Binary32.DotError.ideal,
    List.map_ofFn,List.sum_ofFn] using error⟩

theorem Inputs.affine_facts (i : Inputs d) (fold : Dot.Fold (pairs d) 0 z)
    (allowed : Binary32.Error.AffineResults z (d (slot 1)) (d (slot 2)) p a) :
    finiteReal a = some i.affine ∧ |i.affine-(i.idealDot+i.b)| ≤ i.budget := by
  obtain ⟨hz,ez⟩ := i.dot_facts fold
  have ho : finiteReal (d (slot 1)) = some 1 := i.one ▸ one_real
  have value := Binary32.SquareError.affine_value z (d (slot 1)) (d (slot 2)) p a
    i.dot 1 i.bh hz ho i.bReal i.multiplyRange i.additionRange allowed
  obtain ⟨_,_,r,hr,error⟩ := Binary32.Error.affine_results z (d (slot 1)) (d (slot 2)) p a
    i.dot 1 i.bh i.idealDot 1 i.b i.dotBudget 0 i.eb hz ho i.bReal
    i.multiplyRange i.additionRange ez (by simp) i.bError allowed
  have eq : r = i.affine := Option.some.inj (hr.symm.trans value)
  exact ⟨value,by simpa [eq,Inputs.budget] using error⟩

theorem forward_accuracy (i : Inputs d) (ev : Evaluation d (forwardStages s.size) out) :
    finiteReal (out (slot 4)) = some (max i.affine 0) ∧
      |max i.affine 0 - Tensor.item ((VectorVJP.graph s).forward (VectorVJP.inputs i.x i.w i.b))| ≤ i.budget := by
  obtain ⟨z,p,a,hz,ha,hy⟩ := forward_values ev
  obtain ⟨value,error⟩ := i.affine_facts hz ha
  refine ⟨hy ▸ Binary32.Relu.forward_real a _ value,?_⟩
  rw [VectorVJP.forward_value,i.graph_affine]
  exact Binary32.Relu.forward_error _ _ _ error

/-- Initial-input conditions for a branch-stable backward and finite gradient stages. -/
structure BackwardInputs {s : Shape} (d : Buffer s.size) extends Inputs d where
  dh : ℝ
  upstream : ℝ
  ed : ℝ
  seedReal : finiteReal (d (slot 5)) = some dh
  seedError : |dh-upstream| ≤ ed
  margin : toInputs.budget < |toInputs.idealDot+b|
  dxRange : ∀ j, StageRange (ReluVJP.gate toInputs.affine dh) (entries j).lh
  dwRange : ∀ j, StageRange (ReluVJP.gate toInputs.affine dh) (entries j).rh

noncomputable def BackwardInputs.actualGate (i : BackwardInputs d) : ℝ := ReluVJP.gate i.affine i.dh
noncomputable def BackwardInputs.idealGate (i : BackwardInputs d) : ℝ := ReluVJP.gate (i.idealDot+i.b) i.upstream
noncomputable def BackwardInputs.dxBudget (i : BackwardInputs d) (j : Fin s.size) : ℝ :=
  stageBudget i.actualGate (i.entries j).lh i.idealGate (i.entries j).l i.ed (i.entries j).el
noncomputable def BackwardInputs.dwBudget (i : BackwardInputs d) (j : Fin s.size) : ℝ :=
  stageBudget i.actualGate (i.entries j).rh i.idealGate (i.entries j).r i.ed (i.entries j).er
noncomputable def BackwardInputs.dxValue (i : BackwardInputs d) (j : Fin s.size) : ℝ :=
  roundedProduct i.actualGate (i.entries j).lh
noncomputable def BackwardInputs.dwValue (i : BackwardInputs d) (j : Fin s.size) : ℝ :=
  roundedProduct i.actualGate (i.entries j).rh

/-- Simultaneous coordinatewise bounds, including the stored bias gradient. -/
def BackwardAccuracy (i : BackwardInputs (s := s) d) (out : Buffer s.size) : Prop :=
  finiteReal (out (slot 6)) = some i.actualGate ∧ |i.actualGate-i.idealGate| ≤ i.ed ∧
  (∀ j, finiteReal (out (dx j)) = some (i.dxValue j) ∧
    |i.dxValue j-i.idealGate*(i.entries j).l| ≤ i.dxBudget j) ∧
  (∀ j, finiteReal (out (dw j)) = some (i.dwValue j) ∧
    |i.dwValue j-i.idealGate*(i.entries j).r| ≤ i.dwBudget j)

theorem backward_accuracy (i : BackwardInputs d) (ev : Evaluation d (backwardStages s.size) out) :
    BackwardAccuracy i out ∧ VectorVJP.affine i.x i.w i.b ≠ 0 := by
  obtain ⟨z,p,a,hz,ha,db,grads⟩ := backward_values ev
  obtain ⟨value,error⟩ := i.toInputs.affine_facts hz ha
  have stable := Binary32.Relu.sign_stable _ _ _ error i.margin
  have hdb : finiteReal (out (slot 6)) = some i.actualGate := by
    rw [db]
    exact Binary32.Relu.gate_real a (d (slot 5)) i.affine i.dh value i.seedReal
  have seedBound : |i.actualGate-i.idealGate| ≤ i.ed := by
    have nonneg := (abs_nonneg _).trans i.seedError
    dsimp [BackwardInputs.actualGate,BackwardInputs.idealGate,ReluVJP.gate]
    by_cases active : 0 < i.idealDot+i.b <;> simp [stable,active,i.seedError,nonneg]
  have away : VectorVJP.affine i.x i.w i.b ≠ 0 := by
    rw [Inputs.graph_affine]
    intro h
    have hn := (abs_nonneg _).trans error
    have hm := i.margin
    rw [h,abs_zero] at hm
    linarith
  refine ⟨⟨hdb,seedBound,?_,?_⟩,away⟩
  · intro j
    obtain ⟨m,hm⟩ := grads (.dx j)
    have hw : finiteReal (d (weight j)) = some (i.entries j).lh := i.leftWords j ▸ (i.entries j).leftReal
    exact Binary32.BackwardError.stage_error (out (slot 6)) (d (weight j)) m (out (dx j))
      i.actualGate (i.entries j).lh i.idealGate (i.entries j).l i.ed (i.entries j).el
      hdb hw (i.dxRange j) seedBound (i.entries j).leftError (by simpa [i.zero,Gradient.source,Gradient.dest] using hm)
  · intro j
    obtain ⟨m,hm⟩ := grads (.dw j)
    have hx : finiteReal (d (input j)) = some (i.entries j).rh := i.rightWords j ▸ (i.entries j).rightReal
    exact Binary32.BackwardError.stage_error (out (slot 6)) (d (input j)) m (out (dw j))
      i.actualGate (i.entries j).rh i.idealGate (i.entries j).r i.ed (i.entries j).er
      hdb hx (i.dwRange j) seedBound (i.entries j).rightError (by simpa [i.zero,Gradient.source,Gradient.dest] using hm)

/-- The reference values in the error bounds are the actual generated VJP. -/
theorem BackwardInputs.generated (i : BackwardInputs (s := s) d) :
    (VectorVJP.graph s).vjpWithSeed (VectorVJP.inputs i.x i.w i.b) (Tensor.scalar i.upstream) =
      VectorVJP.inputs (VectorVJP.scale i.idealGate i.w) (VectorVJP.scale i.idealGate i.x) i.idealGate := by
  simpa [VectorVJP.sensitivities,BackwardInputs.idealGate] using
    VectorVJP.generated_vjp i.x i.w i.b i.upstream

theorem stored_forward_accuracy (i : Inputs (s := s) d) (small : s.size < 2^32)
    (present : before.cells allocation = some ⟨thread.device,words d tail⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before ((forwardStages s.size).map (request target thread allocation seeds)) after) :
    ∃ out : Buffer s.size, after.cells allocation = some ⟨thread.device,words out tail⟩ ∧
      finiteReal (out (slot 4)) = some (max i.affine 0) ∧
      |max i.affine 0-Tensor.item ((VectorVJP.graph s).forward (VectorVJP.inputs i.x i.w i.b))| ≤ i.budget := by
  obtain ⟨out,ev,saved⟩ := pipeline_correct small (forwardStages s.size) present eligible chain
  exact ⟨out,saved,forward_accuracy i ev⟩

theorem stored_backward_accuracy (i : BackwardInputs (s := s) d) (small : s.size < 2^32)
    (present : before.cells allocation = some ⟨thread.device,words d tail⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before ((backwardStages s.size).map (request target thread allocation seeds)) after) :
    ∃ out : Buffer s.size, after.cells allocation = some ⟨thread.device,words out tail⟩ ∧
      BackwardAccuracy i out ∧ VectorVJP.affine i.x i.w i.b ≠ 0 := by
  obtain ⟨out,ev,saved⟩ := pipeline_correct small (backwardStages s.size) present eligible chain
  exact ⟨out,saved,backward_accuracy i ev⟩

/-- The same initial tensors used by TorchLean supply the error-bound coordinates. -/
@[simp] theorem Inputs.x_coordinate (i : Inputs d) (j : Fin s.size) :
    tensorToVec i.x j = (i.entries j).r := by simp [Inputs.x,vecOfFun]
@[simp] theorem Inputs.w_coordinate (i : Inputs d) (j : Fin s.size) :
    tensorToVec i.w j = (i.entries j).l := by simp [Inputs.w,vecOfFun]

/-- End-to-end: stored gradients satisfy the bounds, and their real reference
is the ordinary mathematical derivative of the actual upstream graph. -/
theorem stored_backward_adjoint (i : BackwardInputs (s := s) d) (small : s.size < 2^32)
    (present : before.cells allocation = some ⟨thread.device,words d tail⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before ((backwardStages s.size).map (request target thread allocation seeds)) after) :
    (∃ out : Buffer s.size, after.cells allocation = some ⟨thread.device,words out tail⟩ ∧ BackwardAccuracy i out) ∧
    flattenCtx (VectorVJP.sensitivities i.x i.w i.b i.upstream) =
      (fderiv ℝ (fun v => tensorToVec ((VectorVJP.graph s).forward (unflattenCtx v)))
        (flattenCtx (VectorVJP.inputs i.x i.w i.b))).adjoint (tensorToVec (Tensor.scalar i.upstream)) := by
  obtain ⟨out,saved,accuracy,away⟩ := stored_backward_accuracy i small present eligible chain
  exact ⟨⟨out,saved,accuracy⟩,VectorVJP.sensitivities_adjoint i.x i.w i.b i.upstream away⟩

/-- Empty tensors still compute a bias-only neuron. -/
theorem empty_forward (x w : Tensor ℝ [0]) (b : ℝ) :
    Tensor.item ((VectorVJP.graph [0]).forward (VectorVJP.inputs x w b)) = max b 0 := by
  rw [VectorVJP.forward_value]
  have hz : (∑ j : Fin (Spec.Shape.size ([0] : Shape)), tensorToVec w j * tensorToVec x j) = 0 :=
    Finset.sum_eq_zero (fun j _ => Fin.elim0 j)
  simp only [VectorVJP.affine,hz,zero_add]

/-- At the kink the generated convention is zero, without a differentiability claim. -/
theorem kink_backward (x w : Tensor ℝ s) (b upstream : ℝ)
    (kink : VectorVJP.affine x w b = 0) :
    (VectorVJP.graph s).vjpWithSeed (VectorVJP.inputs x w b) (Tensor.scalar upstream) =
      VectorVJP.inputs (VectorVJP.scale 0 w) (VectorVJP.scale 0 x) 0 := by
  simp [VectorVJP.generated_vjp,VectorVJP.sensitivities,kink,ReluVJP.gate]

end PtxTorchLean.VectorKernel


