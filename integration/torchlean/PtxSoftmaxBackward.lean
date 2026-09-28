import PtxSoftmaxBackwardReference
import PtxBinary32.SoftmaxBackwardFull
import PtxBinary32.SoftmaxBackwardDotCorrect
import PtxBinary32.SoftmaxBackwardNumeric

/-! Stored gradients of the supplied parallel backward approximate TorchLean's
true real softmax VJP. Every range and arithmetic error obligation follows from
original finite inputs, the forward guard and actual admitted executions. -/
namespace PtxTorchLean.SoftmaxBackward
open Ptx Ptx.Binary32 Ptx.Scalar.Parallel
open Ptx.Numerics.Softmax
open scoped BigOperators
noncomputable section

abbrev KernelRun := Ptx.Scalar.Parallel.SoftmaxBackward.Run
abbrev FullRun := Ptx.Scalar.Parallel.SoftmaxBackward.FullRun

def gradientValue (d : Nat) (pv gv : Fin (Sum.width d) → ℝ) (i : Fin (Sum.width d)) : ℝ :=
  SoftmaxBackwardNumeric.gradient (pv i) (gv i) (BackwardDot.vector_rounded d gv pv)

def allowance (d : Nat) (ideal pv gv epsilon : Fin (Sum.width d) → ℝ) (i : Fin (Sum.width d)) : ℝ :=
  backwardBudget pv gv ideal epsilon (fun _=>0)
    (fun j=>SoftmaxBackwardNumeric.subError (gv j) (BackwardDot.vector_rounded d gv pv))
    (fun j=>SoftmaxBackwardNumeric.mulError (pv j) (gv j) (BackwardDot.vector_rounded d gv pv))
    (BackwardDot.vector_budget d gv pv) i

/-- The backward's local numerical contract discharges the abstract gradient
error theorem from actual stored instructions and original operand bounds. -/
theorem kernel_accuracy (d : Nat) (bound : Sum.Bounds d)
    (p g : Fin (Sum.width d) → Word) (pv gv ideal epsilon : Fin (Sum.width d) → ℝ)
    (finiteP : ∀i,finiteReal (p i)=some (pv i))
    (finiteG : ∀i,finiteReal (g i)=some (gv i))
    (smallP : ∀i,|pv i|≤4) (smallG : ∀i,|gv i|≤(2:ℝ)^60)
    (forwardError : ∀i,|pv i-ideal i|≤epsilon i)
    (run : KernelRun d bound p g final) :
    ∀i, ∃word, final[Scalar.Parallel.SoftmaxBackward.gradientBase d+i.val]?=some word ∧
      finiteReal word=some (gradientValue d pv gv i) ∧
      |gradientValue d pv gv i-ideal i*(gv i-∑j,ideal j*gv j)|≤allowance d ideal pv gv epsilon i := by
  obtain ⟨len,frame,q,dotAllowed,qStored,stages⟩ := Scalar.Parallel.SoftmaxBackward.correct run
  obtain ⟨qFinite,qSmall,qError⟩ := SoftmaxBackwardDot.output_accuracy d bound p g pv gv q
    finiteP finiteG smallP smallG dotAllowed
  have coords (i : Fin (Sum.width d)) := SoftmaxBackwardNumeric.accuracy (p i) (g i) q
    final[Scalar.Parallel.SoftmaxBackward.gradientBase d+i.val]! (pv i) (gv i)
    (BackwardDot.vector_rounded d gv pv) (finiteP i) (finiteG i) qFinite (smallP i) (smallG i) qSmall
    (by obtain ⟨neg,diff,hn,hd,_,ho⟩ := stages i; exact ⟨neg,diff,hn,hd,ho⟩)
  have data : BackwardStages ideal pv gv gv (BackwardDot.vector_rounded d gv pv)
      (fun i=>SoftmaxBackwardNumeric.difference (gv i) (BackwardDot.vector_rounded d gv pv))
      (gradientValue d pv gv) epsilon (fun _=>0) (BackwardDot.vector_budget d gv pv)
      (fun i=>SoftmaxBackwardNumeric.subError (gv i) (BackwardDot.vector_rounded d gv pv))
      (fun i=>SoftmaxBackwardNumeric.mulError (pv i) (gv i) (BackwardDot.vector_rounded d gv pv)) :=
    ⟨forwardError,by intro i; simp,qError,fun i=>(coords i).2.1,fun i=>(coords i).2.2⟩
  intro i
  refine ⟨final[Scalar.Parallel.SoftmaxBackward.gradientBase d+i.val]!,?_,(coords i).1,?_⟩
  · apply Scalar.SoftmaxStorage.some_bang
    rw [len]; have := i.isLt; unfold Scalar.Parallel.SoftmaxBackward.gradientBase; omega
  · exact backward_coordinate_error data i

/-- The final prefix retains the actual approximate forward weights and supplied
sensitivities. Its gradient suffix approximates the actual TorchLean backward.
The error allowance uses the inherited forward budget and each actual rounded
backward operation, not a supplied bound on the completed gradient. -/
def Accurate (d : Nat) (input incoming : Fin (Sum.width d) → Word)
    (values gv : Fin (Sum.width d) → ℝ) (final : List Word) : Prop :=
  ∃ (m : ℝ) (u : Fin (Sum.width d) → ℝ),
    finiteReal (Scalar.SoftmaxPipeline.maximumWord d input)=some m ∧
    final.length=4*Sum.width d+2 ∧
    (∀i,finiteReal final[i.val]! =some (SoftmaxPipeline.resultValue d u i) ∧
      |SoftmaxPipeline.resultValue d u i|≤4 ∧
      |SoftmaxPipeline.resultValue d u i-Softmax.rowForward values i|≤
        SoftmaxPipeline.coordinateAllowance d values m u i) ∧
    (∀i,final[Sum.width d+i.val]?=some (incoming i)) ∧
    ∀i,∃word,final[Scalar.Parallel.SoftmaxBackward.gradientBase d+i.val]?=some word ∧
      finiteReal word=some (gradientValue d (SoftmaxPipeline.resultValue d u) gv i) ∧
      |gradientValue d (SoftmaxPipeline.resultValue d u) gv i-Softmax.rowBackward values gv i|≤
        allowance d (Softmax.rowForward values) (SoftmaxPipeline.resultValue d u) gv
          (SoftmaxPipeline.coordinateAllowance d values m u) i

/-- Every completed admitted full execution satisfies the stored gradient bound.
Only original scores and incoming sensitivities have finite/range premises. -/
theorem correct (d : Nat) (bound : Sum.Bounds d)
    (input incoming : Fin (Sum.width d) → Word) (values gv : Fin (Sum.width d) → ℝ)
    (finite : ∀i,finiteReal (input i)=some (values i))
    (small : ∀i,|values i|≤(2:ℝ)^(124:ℤ))
    (guard : SoftmaxPipeline.AccuracyGuard d values)
    (incomingFinite : ∀i,finiteReal (incoming i)=some (gv i))
    (incomingSmall : ∀i,|gv i|≤(2:ℝ)^60)
    (run : FullRun d bound input incoming final) : Accurate d input incoming values gv final := by
  cases run with
  | @phases forward final forwardRun backwardRun =>
    obtain ⟨m,u,mvalue,reported⟩ := forward_report d bound input values finite small guard forwardRun
    have result := Scalar.Parallel.SoftmaxBackward.correct backwardRun
    have gradients := kernel_accuracy d bound (Scalar.SoftmaxStorage.row (Sum.width d) forward) incoming
      (SoftmaxPipeline.resultValue d u) gv (Softmax.rowForward values)
      (SoftmaxPipeline.coordinateAllowance d values m u)
      (fun i=>(reported i).1) incomingFinite (fun i=>(reported i).2.1) incomingSmall
      (fun i=>(reported i).2.2) backwardRun
    refine ⟨m,u,mvalue,result.1,?_,fun i=>(result.2.1 i).2,?_⟩
    · intro i
      have saved := (result.2.1 i).1
      have same := Scalar.Parallel.SoftmaxBackward.saved_word _ _ _ saved
      rw [same]
      exact reported i
    · intro i
      obtain ⟨word,stored,wordValue,error⟩ := gradients i
      exact ⟨word,stored,wordValue,by rwa [Softmax.rowBackward_formula]⟩

/-- Independent execution existence and the universal theorem yield a complete
accurate forward/backward execution under the original input conditions. -/
theorem accurate_execution_exists (d : Nat) (bound : Sum.Bounds d)
    (input incoming : Fin (Sum.width d) → Word) (values gv : Fin (Sum.width d) → ℝ)
    (finite : ∀i,finiteReal (input i)=some (values i))
    (small : ∀i,|values i|≤(2:ℝ)^(124:ℤ))
    (guard : SoftmaxPipeline.AccuracyGuard d values)
    (incomingFinite : ∀i,finiteReal (incoming i)=some (gv i))
    (incomingSmall : ∀i,|gv i|≤(2:ℝ)^60) :
    ∃final,FullRun d bound input incoming final ∧ Accurate d input incoming values gv final := by
  obtain ⟨final,run⟩ := Scalar.Parallel.SoftmaxBackward.full_execution_exists d bound input incoming values finite small
  exact ⟨final,run,correct d bound input incoming values gv finite small guard incomingFinite incomingSmall run⟩

end
end PtxTorchLean.SoftmaxBackward
