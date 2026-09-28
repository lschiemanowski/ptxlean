import PtxBinary32.SoftmaxPipelineExists
import PtxSoftmaxForward

/-! Stored-output accuracy of the complete reference softmax composition against
the pinned TorchLean tensor specification. The reductions use parallel admitted
runs; the surrounding memory passes are sequential in the composition model. -/
namespace PtxTorchLean.SoftmaxPipeline
open Ptx Ptx.Binary32 Ptx.Scalar
open Ptx.Scalar.Parallel
open TorchLean.Floats (round32 eps32)
open Ptx.Numerics.Softmax
open scoped BigOperators
noncomputable section

/-- A condition on the original real scores and their attained maximum. It
requires no caller-supplied intermediate word or successful execution. -/
def AccuracyGuard (d : Nat) (values : Fin (Sum.width d) → ℝ) : Prop :=
  ∀m, (∀i, values i≤m) → (∃i, values i=m) → SoftmaxForward.totalBudget d values m≤1/2

def resultValue (d : Nat) (u : Fin (Sum.width d) → ℝ) (i : Fin (Sum.width d)) : ℝ :=
  round32 (u i*round32 (1/Sum.rounded d u))

def coordinateAllowance (d : Nat) (values : Fin (Sum.width d) → ℝ)
    (m : ℝ) (u : Fin (Sum.width d) → ℝ) (i : Fin (Sum.width d)) : ℝ :=
  coordinateBudget (SoftmaxForward.delta (values i) m) (SoftmaxForward.totalBudget d values m)
    (eps32 (1/Sum.rounded d u)) (eps32 (u i*round32 (1/Sum.rounded d u)))

/-- Each result is present in the final arena, has a finite real interpretation,
and approximates TorchLean's actual softmax tensor. The existential numerical
intermediates are obtained from actual arithmetic relations in the proof. -/
def Accurate (d : Nat) (input : Fin (Sum.width d) → Word)
    (values : Fin (Sum.width d) → ℝ) (final : List Word) : Prop :=
  final.length=2*Sum.width d+2 ∧
  ∃ (m : ℝ) (u : Fin (Sum.width d) → ℝ)
      (exponential : Fin (Sum.width d) → Word) (denominator : Word),
    finiteReal (Scalar.SoftmaxPipeline.maximumWord d input)=some m ∧
    (∀i, values i≤m) ∧ (∃i, values i=m) ∧
    (∀i, SoftmaxForward.ExpStages (input i) (Scalar.SoftmaxPipeline.maximumWord d input) (exponential i)) ∧
    Sum.Output d exponential denominator ∧
    (∀i, Normalize.Stages (exponential i) denominator (final[i.val]!)) ∧
    (∀i, finiteReal (exponential i)=some (u i)) ∧
    finiteReal denominator=some (Sum.rounded d u) ∧ 1/2≤Sum.rounded d u ∧
    (∀i, ∃word, final[i.val]?=some word ∧ finiteReal word=some (resultValue d u i) ∧
      |resultValue d u i-Softmax.rowForward values i|≤coordinateAllowance d values m u i) ∧
    |(∑i,resultValue d u i)-1|≤∑i,coordinateAllowance d values m u i

/-- Every run of the entire composition has accurate stored output. Maximum,
exponential and sum finiteness and all range checks are derived from the initial
finite input row. The explicit accuracy guard controls the denominator error. -/
theorem correct (d : Nat) (bound : d≤10)
    (input : Fin (Sum.width d) → Word) (values : Fin (Sum.width d) → ℝ)
    (finite : ∀i, finiteReal (input i)=some (values i))
    (small : ∀i, |values i|≤(2:ℝ)^(124:ℤ))
    (guard : AccuracyGuard d values) (run : Scalar.SoftmaxPipeline.Run d input final) :
    Accurate d input values final := by
  obtain ⟨exponential,denominator,expStages,sumStages,normStages,len⟩ :=
    Scalar.SoftmaxPipeline.arithmetic run
  obtain ⟨m,mvalue,bounds,j,_,attained⟩ := SoftmaxReductions.maximum_input_bounds d input values finite small
  have upper : ∀i, values i≤m := fun i => (bounds i).1
  have reaches : ∃i, values i=m := ⟨j,attained.symm⟩
  obtain ⟨u,expValues,denValue,den,outputs,errors,normalization⟩ := SoftmaxForward.correct d bound
    input exponential (fun i => final[i.val]!) (Scalar.SoftmaxPipeline.maximumWord d input)
    denominator values m finite mvalue upper reaches small expStages sumStages normStages
    (guard m upper reaches)
  refine ⟨len,m,u,exponential,denominator,mvalue,upper,reaches,expStages,sumStages,normStages,
    expValues,denValue,den,?_,normalization⟩
  intro i
  have valid : i.val<final.length := by rw [len]; have := i.isLt; omega
  refine ⟨final[i.val]!,?_,outputs i,?_⟩
  · simp [valid]
  · exact Softmax.rowForward_error values m _ _ upper reaches i (errors i)

/-- An entire fetched composition with accurate stored output exists under the
same initial-row conditions. This combines a separate execution-existence proof
with the universal accuracy theorem; accuracy is not built into the run relation. -/
theorem accurate_execution_exists (d : Nat) (bound : d≤10)
    (input : Fin (Sum.width d) → Word) (values : Fin (Sum.width d) → ℝ)
    (finite : ∀i, finiteReal (input i)=some (values i))
    (small : ∀i, |values i|≤(2:ℝ)^(124:ℤ)) (guard : AccuracyGuard d values) :
    ∃final, Scalar.SoftmaxPipeline.Run d input final ∧ Accurate d input values final := by
  obtain ⟨final,run⟩ := Scalar.SoftmaxPipeline.execution_exists d bound input values finite small
  exact ⟨final,run,correct d bound input values finite small guard run⟩

/-- The accuracy condition is satisfied by all equal-score rows in the domain. -/
theorem equal_scores_guard (d : Nat) (bound : d≤10) (score : ℝ) :
    AccuracyGuard d (fun _ => score) := by
  intro m _ attained
  obtain ⟨_,same⟩ := attained
  subst m
  exact SoftmaxForward.equal_scores_guard d bound score

end
end PtxTorchLean.SoftmaxPipeline
