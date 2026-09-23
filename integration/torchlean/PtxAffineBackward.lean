import PtxBinary32.BackwardPipeline
import PtxBinary32.BackwardError
import PtxGradientView

/-! Separately authored recomputing backward: first recompute the affine value,
then run four manually selected kernels. No automatic PTX differentiation. -/
namespace PtxTorchLean.AffineBackward
open Ptx Ptx.Scalar Ptx.Scalar.Sequential Ptx.SequentialStorage
open PtxTorchLean.AffineSquareVJP

abbrev Data := BackwardPipeline.Data

def recomputeArgs (allocation : Nat) (i : Fin 4) : Argument :=
  ⟨allocation, match i.val with | 0 => 0 | 1 => 4 | _ => 8⟩

def withSaved (data : Data) (saved : Word) : Data := {data with saved := saved}

def recomputeStart (data : Data) (allocation : Nat) (registers : Seed) : State :=
  start registers (recomputeArgs allocation) data.words

def recomputeRequest (target : Target) (thread : ThreadLocation) (allocation : Nat)
    (registers : Seed) : Request :=
  ⟨target, Affine.program, thread, allocation, 4, recomputeArgs allocation, registers⟩

def requests (target : Target) (thread : ThreadLocation) (allocation : Nat)
    (recomputeSeed : Seed) (backwardSeeds : Fin 4 → Seed) : List Request :=
  recomputeRequest target thread allocation recomputeSeed ::
    BackwardPipeline.requests target thread allocation backwardSeeds

variable {data : Data} {allocation : Nat} {registers : Seed} {target : Target}
  {thread : ThreadLocation} {before after : Store} {final : State} {events : List Mixed.Event}
  {product saved : Word}

theorem recompute_initial : Affine.Initial (recomputeStart data allocation registers) := by
  constructor
  · rfl
  · intro i; fin_cases i <;>
      simp [recomputeStart, start, recomputeArgs, BackwardPipeline.Data.words, ValidAddress]

theorem recompute_run_iff (eligible : Mixed.Eligible target) :
    Mixed.Run target Affine.program (recomputeStart data allocation registers) final .halted events ↔
      ∃ product saved, Binary32.Error.AffineResults data.x data.w data.saved product saved ∧
        final = Affine.finish (recomputeStart data allocation registers) product saved ∧
        events = Affine.trace (recomputeStart data allocation registers) product saved := by
  simpa [Affine.input, recomputeStart, start, recomputeArgs, BackwardPipeline.Data.words] using
    Affine.run_iff (recomputeStart data allocation registers) target recompute_initial eligible final .halted events

theorem recompute_memory :
    (Affine.finish (recomputeStart data allocation registers) product saved).memory =
      (withSaved data saved).words := by
  simp [Affine.finish, Affine.afterAdd, Affine.afterMultiply, Affine.afterBias,
    Affine.afterRight, Affine.afterLeft, Affine.outputIndex, recomputeStart, start,
    recomputeArgs, withSaved, BackwardPipeline.Data.words]

/-- The bias slot is overwritten only after it has been read; the saved affine
value and its provenance follow from the actual run and exact writeback. -/
theorem recompute_correct
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target)
    (launch : SuccessfulLaunch (recomputeRequest target thread allocation registers) before after final events) :
    ∃ product saved, Binary32.Error.AffineResults data.x data.w data.saved product saved ∧
      after.cells allocation = some ⟨thread.device, (withSaved data saved).words⟩ ∧
      final = Affine.finish (recomputeStart data allocation registers) product saved ∧
      events = Affine.trace (recomputeStart data allocation registers) product saved := by
  obtain ⟨product, saved, allowed, state, trace⟩ := (recompute_run_iff eligible).mp (launch.run_from present)
  refine ⟨product, saved, allowed, ?_, state, trace⟩
  simpa only [recomputeRequest, state, recompute_memory] using launch.writeback_lookup present

/-- Construct one actual completed recomputation for every encoded input. -/
theorem recompute_exists
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target) :
    ∃ after final events product saved,
      SuccessfulLaunch (recomputeRequest target thread allocation registers) before after final events ∧
      Binary32.Error.AffineResults data.x data.w data.saved product saved ∧
      after.cells allocation = some ⟨thread.device, (withSaved data saved).words⟩ := by
  obtain ⟨product, mul⟩ := Binary32.results_exists .mul data.x data.w
  obtain ⟨saved, add⟩ := Binary32.results_exists .add product data.saved
  have run := (recompute_run_iff (data := data) (allocation := allocation) (registers := registers)
    (final := Affine.finish (recomputeStart data allocation registers) product saved)
    (events := Affine.trace (recomputeStart data allocation registers) product saved) eligible).mpr
      ⟨product, saved, ⟨mul,add⟩, rfl, rfl⟩
  obtain ⟨after, launch⟩ := launch_exists (request := recomputeRequest target thread allocation registers)
    present rfl (fun _ => rfl) run
  refine ⟨after, _, _, product, saved, launch, ⟨mul,add⟩, ?_⟩
  simpa only [recomputeRequest, recompute_memory] using launch.writeback_lookup present

noncomputable def budgetX (xh wh bh dh x w b d ex ew eb ed : ℝ) : ℝ :=
  Binary32.BackwardError.parameterBudget wh (Binary32.SquareError.roundedAffine xh wh bh) dh
    w (x*w+b) d ew (Binary32.Error.affineBudget xh wh bh x w ex ew eb) ed

noncomputable def budgetW (xh wh bh dh x w b d ex ew eb ed : ℝ) : ℝ :=
  Binary32.BackwardError.parameterBudget xh (Binary32.SquareError.roundedAffine xh wh bh) dh
    x (x*w+b) d ex (Binary32.Error.affineBudget xh wh bh x w ex ew eb) ed

noncomputable def budgetB (xh wh bh dh x w b d ex ew eb ed : ℝ) : ℝ :=
  Binary32.BackwardError.baseBudget (Binary32.SquareError.roundedAffine xh wh bh) dh
    (x*w+b) d (Binary32.Error.affineBudget xh wh bh x w ex ew eb) ed

/-- Arithmetic-to-TorchLean helper. Its operation-result premises are discharged
from actual launches by the stored-output theorem below. Saved-value meaning,
error and finiteness are derived here from the actual recomputation. -/
theorem results_approximate
    (data : Data) (product saved pQ q pDb db pDx dx pDw dw : Word)
    (xh wh bh dh x w b d ex ew eb ed : ℝ)
    (xReal : Binary32.finiteReal data.x = some xh)
    (wReal : Binary32.finiteReal data.w = some wh)
    (bReal : Binary32.finiteReal data.saved = some bh)
    (dReal : Binary32.finiteReal data.seed = some dh)
    (multiplyRange : |xh*wh| ≤ Binary32.Bounds.maxFinite)
    (additionRange : |xh*wh| + TorchLean.Floats.eps32 (xh*wh) + |bh| ≤ Binary32.Bounds.maxFinite)
    (backwardRange : Binary32.BackwardError.Guards xh wh (Binary32.SquareError.roundedAffine xh wh bh) dh)
    (xError : |xh-x| ≤ ex) (wError : |wh-w| ≤ ew)
    (bError : |bh-b| ≤ eb) (dError : |dh-d| ≤ ed)
    (recomputed : Binary32.Error.AffineResults data.x data.w data.saved product saved)
    (backward : Binary32.BackwardError.Results data.x data.w saved data.seed pQ q pDb db pDx dx pDw dw) :
    GradientView.Approximates ⟨dx,dw,db⟩
      (graph.vjpWithSeed (inputs x w b) (TorchLean.Tensor.scalar d))
      (budgetX xh wh bh dh x w b d ex ew eb ed)
      (budgetW xh wh bh dh x w b d ex ew eb ed)
      (budgetB xh wh bh dh x w b d ex ew eb ed) ∧
    graph.vjpChecked (inputs x w b) () (TorchLean.Tensor.scalar d) =
      .ok (sensitivities x w b d, TorchLean.Tensor.scalar ((x*w+b)^2)) := by
  have savedReal := Binary32.SquareError.affine_value data.x data.w data.saved product saved
    xh wh bh xReal wReal bReal multiplyRange additionRange recomputed
  obtain ⟨_, _, value, valueReal, valueError⟩ := Binary32.Error.affine_results
    data.x data.w data.saved product saved xh wh bh x w b ex ew eb
    xReal wReal bReal multiplyRange additionRange xError wError bError recomputed
  have eq : value = Binary32.SquareError.roundedAffine xh wh bh :=
    Option.some.inj (valueReal.symm.trans savedReal)
  subst value
  obtain ⟨_, dbReal, dxReal, dwReal, dxError, dwError, dbError⟩ := Binary32.BackwardError.results_error
    data.x data.w saved data.seed pQ q pDb db pDx dx pDw dw
    xh wh (Binary32.SquareError.roundedAffine xh wh bh) dh x w (x*w+b) d ex ew
    (Binary32.Error.affineBudget xh wh bh x w ex ew eb) ed
    xReal wReal savedReal dReal backwardRange xError wError valueError dError backward
  exact GradientView.generated_of_bounds_checked ⟨dx,dw,db⟩ _ _ _ x w b d _ _ _
    dxReal dwReal dbReal dxError dwError dbError

variable {backwardSeeds : Fin 4 → Seed}

/-- Every completed five-launch chain recomputes its saved affine value and then
uses those actual bits in each separately selected backward stage. -/
theorem pipeline_correct
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before (requests target thread allocation registers backwardSeeds) after) :
    ∃ product saved pQ q pDb db pDx dx pDw dw,
      Binary32.Error.AffineResults data.x data.w data.saved product saved ∧
      Binary32.BackwardError.Results data.x data.w saved data.seed pQ q pDb db pDx dx pDw dw ∧
      after.cells allocation = some ⟨thread.device,
        (BackwardPipeline.outputData (withSaved data saved) q db dx dw).words⟩ := by
  obtain ⟨middle, final, events, first, rest⟩ := Chain.cons_iff.mp chain
  obtain ⟨product, saved, recomputed, savedCell, _, _⟩ := recompute_correct present eligible first
  obtain ⟨pQ,q,pDb,db,pDx,dx,pDw,dw,allowed,written⟩ :=
    BackwardPipeline.pipeline_correct savedCell eligible rest
  exact ⟨product,saved,pQ,q,pDb,db,pDx,dx,pDw,dw,recomputed,allowed,written⟩

/-- Execution existence requires no finite-value, saved-forward or desired
output premise, for arbitrary old result words and independent register seeds. -/
theorem pipeline_exists
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target) :
    ∃ after, Chain before (requests target thread allocation registers backwardSeeds) after := by
  obtain ⟨middle, final, events, product, saved, first, _, savedCell⟩ :=
    recompute_exists (registers := registers) present eligible
  obtain ⟨after, rest⟩ := BackwardPipeline.pipeline_exists (seeds := backwardSeeds) savedCell eligible
  exact ⟨after, .cons first rest⟩

/-- Other logical allocations are preserved by all five actual writebacks. -/
theorem pipeline_other_allocation
    (chain : Chain before (requests target thread allocation registers backwardSeeds) after)
    (other : Nat) (different : other ≠ allocation) : after.cells other = before.cells other := by
  obtain ⟨middle, final, events, first, rest⟩ := Chain.cons_iff.mp chain
  exact (BackwardPipeline.pipeline_other_allocation rest other different).trans (first.other_cell different)

/-- Actual stored-gradient approximation of the actual generated TorchLean VJP.
Only initial input interpretations, deviations and range guards are supplied.
In particular, neither a correct saved value nor successful AD is a premise. -/
theorem stored_backward_approximation
    (present : before.cells allocation = some ⟨thread.device, data.words⟩)
    (eligible : Mixed.Eligible target)
    (chain : Chain before (requests target thread allocation registers backwardSeeds) after)
    (xh wh bh dh x w b d ex ew eb ed : ℝ)
    (xReal : Binary32.finiteReal data.x = some xh)
    (wReal : Binary32.finiteReal data.w = some wh)
    (bReal : Binary32.finiteReal data.saved = some bh)
    (dReal : Binary32.finiteReal data.seed = some dh)
    (multiplyRange : |xh*wh| ≤ Binary32.Bounds.maxFinite)
    (additionRange : |xh*wh| + TorchLean.Floats.eps32 (xh*wh) + |bh| ≤ Binary32.Bounds.maxFinite)
    (backwardRange : Binary32.BackwardError.Guards xh wh (Binary32.SquareError.roundedAffine xh wh bh) dh)
    (xError : |xh-x| ≤ ex) (wError : |wh-w| ≤ ew)
    (bError : |bh-b| ≤ eb) (dError : |dh-d| ≤ ed) :
    ∃ saved q db dx dw,
      after.cells allocation = some ⟨thread.device,
        (BackwardPipeline.outputData (withSaved data saved) q db dx dw).words⟩ ∧
      GradientView.Approximates ⟨dx,dw,db⟩
        (graph.vjpWithSeed (inputs x w b) (TorchLean.Tensor.scalar d))
        (budgetX xh wh bh dh x w b d ex ew eb ed)
        (budgetW xh wh bh dh x w b d ex ew eb ed)
        (budgetB xh wh bh dh x w b d ex ew eb ed) ∧
      graph.vjpChecked (inputs x w b) () (TorchLean.Tensor.scalar d) =
        .ok (sensitivities x w b d, TorchLean.Tensor.scalar ((x*w+b)^2)) := by
  obtain ⟨product,saved,pQ,q,pDb,db,pDx,dx,pDw,dw,recomputed,allowed,written⟩ :=
    pipeline_correct present eligible chain
  exact ⟨saved,q,db,dx,dw,written,results_approximate data product saved pQ q pDb db pDx dx pDw dw
    xh wh bh dh x w b d ex ew eb ed xReal wReal bReal dReal multiplyRange additionRange
    backwardRange xError wError bError dError recomputed allowed⟩

/-- The bias field has its initial role here, before the prefix overwrites it. -/
def fixture (old : Word) : Data :=
  ⟨0x40000000,0x40400000,0x3f800000,0x40000000,old,old,old,old,[]⟩

/-- Actual five-launch example: x=2, weight=3, bias=1, seed=2 yields stored
input/weight/bias gradients 84,56,28. All incoming registers and old outputs
remain arbitrary. -/
theorem five_launch_example (old : Word) (registers : Seed) (backwardSeeds : Fin 4 → Seed) :
    ∃ after, Chain (reserve empty 0 (fixture old).words).2
      (requests ⟨94,70⟩ ⟨0,0,0,0,0⟩ 0 registers backwardSeeds) after ∧
      after.cells 0 = some ⟨0,
        (BackwardPipeline.outputData (withSaved (fixture old) 0x40e00000)
          0x40800000 0x41e00000 0x42a80000 0x42600000).words⟩ := by
  have recomputed : Binary32.Error.AffineResults (fixture old).x (fixture old).w
      (fixture old).saved 0x40c00000 0x40e00000 := by
    constructor
    · change Binary32.Envelope (Binary32.reference .mul 0x40000000 0x40400000) 0x40c00000
      exact Binary32.envelope_self _
    · change Binary32.Envelope (Binary32.reference .add 0x40c00000 0x3f800000) 0x40e00000
      exact Binary32.envelope_self _
  have run := (recompute_run_iff (data := fixture old) (allocation := 0) (registers := registers)
    (final := Affine.finish (recomputeStart (fixture old) 0 registers) 0x40c00000 0x40e00000)
    (events := Affine.trace (recomputeStart (fixture old) 0 registers) 0x40c00000 0x40e00000)
    (target := ⟨94,70⟩) (by constructor <;> decide)).mpr
      ⟨0x40c00000,0x40e00000,recomputed,rfl,rfl⟩
  have present : (reserve empty 0 (fixture old).words).2.cells 0 =
      some (⟨0,(fixture old).words⟩ : Cell) := rfl
  obtain ⟨middle, first⟩ := launch_exists
    (request := recomputeRequest ⟨94,70⟩ ⟨0,0,0,0,0⟩ 0 registers) present rfl (fun _ => rfl) run
  have savedCell : middle.cells 0 = some ⟨0,(withSaved (fixture old) 0x40e00000).words⟩ := by
    simpa only [recomputeRequest, recompute_memory] using first.writeback_lookup present
  have allowed : BackwardPipeline.Results (fixture old).x (fixture old).w 0x40e00000 (fixture old).seed
      0x40800000 0x40800000 0x41e00000 0x41e00000 0x42a80000 0x42a80000 0x42600000 0x42600000 := by
    change BackwardPipeline.Results 0x40000000 0x40400000 0x40e00000 0x40000000
      0x40800000 0x40800000 0x41e00000 0x41e00000 0x42a80000 0x42a80000 0x42600000 0x42600000
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,?_,?_⟩
    all_goals exact Binary32.envelope_self _
  obtain ⟨after, rest, written⟩ := BackwardPipeline.pipeline_of_results
    (data := withSaved (fixture old) 0x40e00000) (allocation := 0)
    (thread := ⟨0,0,0,0,0⟩) (seeds := backwardSeeds) savedCell
    (by constructor <;> decide : Mixed.Eligible ⟨94,70⟩) allowed
  exact ⟨after,.cons first rest,written⟩

end PtxTorchLean.AffineBackward
