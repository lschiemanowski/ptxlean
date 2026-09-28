import PtxBinary32.SoftmaxPipelineExists

/-! End-to-end boundary checks concern actual composed executions and final
stored words. All finite bounded singleton scores normalize to encoded one. -/
namespace Ptx.Scalar.SoftmaxPipeline.Checks
open Parallel Ptx.Binary32

local instance : NeZero (Sum.width 0) := ⟨by norm_num [Sum.width]⟩

private theorem mul_one_one (out : Word) (allowed : Results .mul 0x3f800000 0x3f800000 out) :
    out=0x3f800000 := by
  have eq : reference .mul 0x3f800000 0x3f800000=0x3f800000 := by decide
  unfold Results at allowed
  rw [eq] at allowed
  exact envelope_finite_eq _ _ (by decide) allowed

private theorem add_one_zero (out : Word) (allowed : Results .add 0x3f800000 0 out) :
    out=0x3f800000 := by
  have eq : reference .add 0x3f800000 0=0x3f800000 := by decide
  unfold Results at allowed
  rw [eq] at allowed
  exact envelope_finite_eq _ _ (by decide) allowed

private theorem reciprocal_one (out : Word) (allowed : Ptx.Binary32.Reciprocal.Results 0x3f800000 out) :
    out=0x3f800000 := by
  have eq : Ptx.Binary32.Reciprocal.reference 0x3f800000=0x3f800000 := by decide
  unfold Ptx.Binary32.Reciprocal.Results at allowed
  rw [eq] at allowed
  exact envelope_finite_eq _ _ (by decide) allowed

/-- Every composed singleton execution stores exactly positive one, independently
of the original finite score, its zero sign, and permitted scheduling choices. -/
theorem singleton_exact (input : Fin (Sum.width 0) → Word) (x : ℝ)
    (finite : finiteReal (input 0)=some x) (small : |x|≤(2:ℝ)^(124:ℤ))
    (run : Run 0 input final) : final[0]?=some (0x3f800000 : Word) := by
  obtain ⟨exponential,denominator,expStage,sumStage,normStage,len⟩ := arithmetic run
  have maximumEq : maximumWord 0 input=input 0 := by
    change (Sum.global 0 input)[0]! = input 0
    have h := Sum.global_input 0 input 0
    simpa only [Fin.val_zero,List.getElem!_eq_getElem?_getD,Option.getD_some] using
      congrArg (fun w => w.getD (default : Word)) h
  have expOne : ∀i, exponential i=(0x3f800000 : Word) := by
    intro i
    have iz : i=0 := Fin.eq_zero i
    subst i
    obtain ⟨negative,shifted,product,r₀,r₁,r₂,r₃⟩ := expStage 0
    exact Ptx.Binary32.ShiftedExp.equal_scores (input 0) (maximumWord 0 input) negative shifted product
      (exponential 0) x finite (by rw [maximumEq]; exact finite) small r₀ r₁ r₂ r₃
  have denominatorOne : denominator=(0x3f800000 : Word) := by
    obtain ⟨dot,tree,added⟩ := sumStage
    have only : (List.ofFn exponential)[0]! = (0x3f800000 : Word) := by
      simp only [List.getElem!_eq_getElem?_getD,List.getElem?_ofFn,
        dite_eq_left (show 0<Sum.width 0 by norm_num [Sum.width]),Option.getD_some,expOne]
    change Reduction.Eval (.leaf (0x3f800000,(List.ofFn exponential)[0]!)) dot at tree
    rw [only] at tree
    cases tree with
    | leaf product =>
      rw [mul_one_one dot product] at added
      exact add_one_zero denominator added
  have normalized := normStage 0
  rw [expOne,denominatorOne] at normalized
  obtain ⟨inverse,inverted,multiplied⟩ := normalized
  rw [reciprocal_one inverse inverted] at multiplied
  have result : final[0]! = (0x3f800000 : Word) := mul_one_one _ multiplied
  rw [SoftmaxStorage.some_bang final 0 (by rw [len]; simp [Sum.width]),result]

/-- The singleton conclusion is inhabited by a constructed whole-pipeline run. -/
theorem singleton_exists (input : Fin (Sum.width 0) → Word) (x : ℝ)
    (finite : finiteReal (input 0)=some x) (small : |x|≤(2:ℝ)^(124:ℤ)) :
    ∃final, Run 0 input final ∧ final[0]?=some (0x3f800000 : Word) := by
  obtain ⟨final,run⟩ := execution_exists 0 (by unfold Sum.Bounds; decide) input (fun _ => x)
    (by intro i; have : i=0 := Fin.eq_zero i; simpa [this] using finite)
    (fun _ => small)
  exact ⟨final,run,singleton_exact input x finite small run⟩

end Ptx.Scalar.SoftmaxPipeline.Checks
