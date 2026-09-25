import PtxReluKernel

/-! Numerical consequences of the actual ReLU-neuron pipeline. The activation
margin is derived from the affine error budget, not an assumed branch agreement. -/
namespace PtxTorchLean.ReluKernel
open Ptx Ptx.Scalar Ptx.Scalar.Sequential Ptx.SequentialStorage
open Binary32 (finiteReal)
open Binary32.BackwardError (StageRange stageBudget roundedProduct)

private theorem eval_cons : Evaluation d (stage::rest) out ↔
    ∃ v, Results d stage v ∧ Evaluation (d.update stage v) rest out := by
  constructor
  · intro h; cases h with | cons hv ht => exact ⟨_,hv,ht⟩
  · rintro ⟨v,hv,ht⟩; exact .cons hv ht
private theorem eval_nil : Evaluation d [] out ↔ out = d := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .nil

theorem forward_values (ev : Evaluation d forwardStages out) :
    ∃ p a, Binary32.Error.AffineResults d.w d.x d.b p a ∧
      out = {d with a := a, y := Binary32.Relu.forward a} := by
  simp only [forwardStages, eval_cons, eval_nil, Results, Data.update] at ev
  rcases ev with ⟨a,⟨p,hp⟩,y,hy,ho⟩
  subst y out
  exact ⟨p,a,hp,rfl⟩

theorem backward_values (ev : Evaluation d backwardStages out) :
    ∃ p a px pw,
      Binary32.Error.AffineResults d.w d.x d.b p a ∧
      out.a = a ∧ out.db = Binary32.Relu.gate a d.seed ∧
      Binary32.Error.AffineResults out.db d.w 0 px out.dx ∧
      Binary32.Error.AffineResults out.db d.x 0 pw out.dw := by
  simp only [backwardStages, eval_cons, eval_nil, Results, Data.update] at ev
  rcases ev with ⟨a,⟨p,hp⟩,db,hdb,dx,⟨px,hx⟩,dw,⟨pw,hw⟩,ho⟩
  subst out db
  exact ⟨p,a,px,pw,hp,rfl,rfl,hx,hw⟩

/-- Input-only real conditions shared by forward and backward accuracy. -/
structure Inputs (d : Data) where
  xh : ℝ
  wh : ℝ
  bh : ℝ
  x : ℝ
  w : ℝ
  b : ℝ
  ex : ℝ
  ew : ℝ
  eb : ℝ
  xReal : finiteReal d.x = some xh
  wReal : finiteReal d.w = some wh
  bReal : finiteReal d.b = some bh
  multiplyRange : |wh*xh| ≤ Binary32.Bounds.maxFinite
  additionRange : |wh*xh| + TorchLean.Floats.eps32 (wh*xh) + |bh| ≤ Binary32.Bounds.maxFinite
  xError : |xh-x| ≤ ex
  wError : |wh-w| ≤ ew
  bError : |bh-b| ≤ eb

noncomputable def Inputs.budget (i : Inputs d) : ℝ :=
  Binary32.Error.affineBudget i.wh i.xh i.bh i.w i.x i.ew i.ex i.eb
noncomputable def Inputs.affine (i : Inputs d) : ℝ :=
  Binary32.SquareError.roundedAffine i.wh i.xh i.bh

private theorem affine_facts (i : Inputs d)
    (allowed : Binary32.Error.AffineResults d.w d.x d.b p a) :
    finiteReal a = some i.affine ∧ |i.affine-(i.w*i.x+i.b)| ≤ i.budget := by
  have value := Binary32.SquareError.affine_value d.w d.x d.b p a
    i.wh i.xh i.bh i.wReal i.xReal i.bReal i.multiplyRange i.additionRange allowed
  obtain ⟨_,_,z,hz,he⟩ := Binary32.Error.affine_results d.w d.x d.b p a
    i.wh i.xh i.bh i.w i.x i.b i.ew i.ex i.eb i.wReal i.xReal i.bReal
    i.multiplyRange i.additionRange i.wError i.xError i.bError allowed
  have eq : z = i.affine := Option.some.inj (hz.symm.trans value)
  exact ⟨value, by simpa [eq, Inputs.budget] using he⟩

theorem forward_accuracy (i : Inputs d) (ev : Evaluation d forwardStages out) :
    ∃ y, finiteReal out.y = some y ∧
      |y - TorchLean.Tensor.item (ReluVJP.graph.forward (ReluVJP.inputs i.x i.w i.b))| ≤ i.budget := by
  obtain ⟨p,a,allowed,rfl⟩ := forward_values ev
  obtain ⟨ha,error⟩ := affine_facts i allowed
  refine ⟨max i.affine 0, Binary32.Relu.forward_real a _ ha, ?_⟩
  rw [ReluVJP.forward_value]
  exact Binary32.Relu.forward_error _ _ _ error

/-- A stricter backward domain: the error budget cannot reach the kink, and both
rounded gradient products stay in range. All conditions concern initial inputs. -/
structure BackwardInputs (d : Data) extends Inputs d where
  dh : ℝ
  upstream : ℝ
  ed : ℝ
  seedReal : finiteReal d.seed = some dh
  seedError : |dh-upstream| ≤ ed
  margin : toInputs.budget < |w*x+b|
  dxRange : StageRange (ReluVJP.gate toInputs.affine dh) wh
  dwRange : StageRange (ReluVJP.gate toInputs.affine dh) xh

noncomputable def BackwardInputs.actualGate (i : BackwardInputs d) : ℝ := ReluVJP.gate i.affine i.dh
noncomputable def BackwardInputs.idealGate (i : BackwardInputs d) : ℝ := ReluVJP.gate (i.w*i.x+i.b) i.upstream
noncomputable def BackwardInputs.dxBudget (i : BackwardInputs d) : ℝ :=
  stageBudget i.actualGate i.wh i.idealGate i.w i.ed i.ew
noncomputable def BackwardInputs.dwBudget (i : BackwardInputs d) : ℝ :=
  stageBudget i.actualGate i.xh i.idealGate i.x i.ed i.ex

/-- This is also an ordinary-derivative domain, not merely a chosen zero convention. -/
theorem BackwardInputs.away (i : BackwardInputs d) : i.w*i.x+i.b ≠ 0 := by
  obtain ⟨p,a,allowed⟩ : ∃ p a, Binary32.Error.AffineResults d.w d.x d.b p a := by
    obtain ⟨p,hp⟩ := Binary32.results_exists .mul d.w d.x
    obtain ⟨a,ha⟩ := Binary32.results_exists .add p d.b
    exact ⟨p,a,hp,ha⟩
  have bound := (affine_facts i.toInputs allowed).2
  have nonneg := (abs_nonneg _).trans bound
  intro hz
  have margin := i.margin
  rw [hz, abs_zero] at margin
  linarith

theorem backward_accuracy (i : BackwardInputs d) (ev : Evaluation d backwardStages out) :
    ∃ dx dw db, finiteReal out.dx = some dx ∧ finiteReal out.dw = some dw ∧
      finiteReal out.db = some db ∧
      |dx-i.idealGate*i.w| ≤ i.dxBudget ∧
      |dw-i.idealGate*i.x| ≤ i.dwBudget ∧ |db-i.idealGate| ≤ i.ed := by
  obtain ⟨p,a,px,pw,allowed,_,db,hx,hw⟩ := backward_values ev
  obtain ⟨ha,error⟩ := affine_facts i.toInputs allowed
  have stable := Binary32.Relu.sign_stable _ _ _ error i.margin
  have hdb : finiteReal out.db = some i.actualGate := by
    rw [db]
    exact Binary32.Relu.gate_real a d.seed i.affine i.dh ha i.seedReal
  have seedBound : |i.actualGate-i.idealGate| ≤ i.ed := by
    have nonneg := (abs_nonneg _).trans i.seedError
    dsimp [BackwardInputs.actualGate, BackwardInputs.idealGate, ReluVJP.gate]
    by_cases active : 0 < i.w*i.x+i.b <;> simp [stable, active, i.seedError, nonneg]
  obtain ⟨dxReal,dxError⟩ := Binary32.BackwardError.stage_error out.db d.w px out.dx
    i.actualGate i.wh i.idealGate i.w i.ed i.ew hdb i.wReal i.dxRange seedBound i.wError hx
  obtain ⟨dwReal,dwError⟩ := Binary32.BackwardError.stage_error out.db d.x pw out.dw
    i.actualGate i.xh i.idealGate i.x i.ed i.ex hdb i.xReal i.dwRange seedBound i.xError hw
  exact ⟨_,_,_,dxReal,dwReal,hdb,dxError,dwError,seedBound⟩

/-- Forward accuracy for every actual completed two-launch execution. -/
theorem stored_forward_accuracy (i : Inputs d)
    (present : before.cells allocation = some ⟨thread.device,d.words⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before (forwardStages.map (request target thread allocation registers)) after) :
    ∃ (out : Data) (y : ℝ), after.cells allocation = some ⟨thread.device,out.words⟩ ∧ finiteReal out.y = some y ∧
      |y-TorchLean.Tensor.item (ReluVJP.graph.forward (ReluVJP.inputs i.x i.w i.b))| ≤ i.budget := by
  obtain ⟨out,ev,saved⟩ := pipeline_correct forwardStages present eligible chain
  obtain ⟨y,hy,error⟩ := forward_accuracy i ev
  exact ⟨out,y,saved,hy,error⟩

/-- Stored gradients of every actual recomputing backward execution approximate
exactly the three components of TorchLean's generated backward. -/
theorem stored_backward_accuracy (i : BackwardInputs d)
    (present : before.cells allocation = some ⟨thread.device,d.words⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before (backwardStages.map (request target thread allocation registers)) after) :
    ∃ (out : Data) (dx dw db : ℝ), after.cells allocation = some ⟨thread.device,out.words⟩ ∧
      finiteReal out.dx = some dx ∧ finiteReal out.dw = some dw ∧ finiteReal out.db = some db ∧
      |dx-i.idealGate*i.w| ≤ i.dxBudget ∧ |dw-i.idealGate*i.x| ≤ i.dwBudget ∧ |db-i.idealGate| ≤ i.ed ∧
      ReluVJP.graph.vjpWithSeed (ReluVJP.inputs i.x i.w i.b) (TorchLean.Tensor.scalar i.upstream) =
        ReluVJP.inputs (i.idealGate*i.w) (i.idealGate*i.x) i.idealGate := by
  obtain ⟨out,ev,saved⟩ := pipeline_correct backwardStages present eligible chain
  obtain ⟨dx,dw,db,hx,hw,hb,ex,ew,eb⟩ := backward_accuracy i ev
  exact ⟨out,dx,dw,db,saved,hx,hw,hb,ex,ew,eb,ReluVJP.generated_vjp _ _ _ _⟩

end PtxTorchLean.ReluKernel
