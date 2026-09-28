import PtxBinary32.SumProgram

/-! The softmax backward dot product is the existing fetched dense program with
one output row and no activation. Its weights are the incoming sensitivities;
its inputs are the stored forward probabilities. The ordered tree and the final
addition of positive zero are actual binary32 instructions. -/
namespace Ptx.Scalar.Parallel.SoftmaxBackwardDot
open Ptx.Binary32

/-- The original probabilities and sensitivities precede a positive-zero bias
and the allocated dot-product output cell. -/
def global (d : Nat) (p g : Fin (Sum.width d) → Word) : List Word :=
  List.ofFn p ++ List.ofFn g ++ [0,0]

abbrev outputIndex (d : Nat) : Nat := Sum.outputIndex d

@[simp] theorem global_length (d : Nat) (p g : Fin (Sum.width d) → Word) :
    (global d p g).length=2*Sum.width d+2 := by simp [global]; omega

@[simp] theorem global_probability (d : Nat) (p g : Fin (Sum.width d) → Word)
    (j : Fin (Sum.width d)) : (global d p g)[j.val]?=some (p j) := by
  simp [global,List.getElem?_append,j.isLt]

@[simp] theorem global_sensitivity (d : Nat) (p g : Fin (Sum.width d) → Word)
    (j : Fin (Sum.width d)) : (global d p g)[Sum.width d+j.val]?=some (g j) := by
  simp [global,List.getElem?_append,Nat.not_lt.mpr (Nat.le_add_right _ _),j.isLt]

@[simp] theorem global_probability_bang (d : Nat) (p g : Fin (Sum.width d) → Word)
    (j : Nat) (hj : j<Sum.width d) : (global d p g)[j]! = (List.ofFn p)[j]! := by
  simp [global,List.getElem!_eq_getElem?_getD,List.getElem?_append,hj]

@[simp] theorem global_sensitivity_bang (d : Nat) (p g : Fin (Sum.width d) → Word)
    (j : Nat) (hj : j<Sum.width d) : (global d p g)[Sum.width d+j]! = (List.ofFn g)[j]! := by
  simp [global,List.getElem!_eq_getElem?_getD,List.getElem?_append,
    Nat.not_lt.mpr (Nat.le_add_right _ _),hj]

@[simp] theorem global_bias (d : Nat) (p g : Fin (Sum.width d) → Word) :
    (global d p g)[2*Sum.width d]! = 0 := by
  have h : ¬ 2*Sum.width d < Sum.width d := by omega
  simp [global,List.getElem!_eq_getElem?_getD,List.getElem?_append,h,
    show 2*Sum.width d-Sum.width d=Sum.width d by omega]

/-- The exact permitted arithmetic results include exceptional words, the
specified product operand order, the balanced sum, and the final bias addition. -/
def Output (d : Nat) (p g : Fin (Sum.width d) → Word) (value : Word) : Prop :=
  ∃ dot, Reduction.Eval (Reduction.balanced d 0
    (fun j => ((List.ofFn g)[j]!, (List.ofFn p)[j]!))) dot ∧ Results .add dot 0 value

private theorem balanced_congr (d offset : Nat) (a b : Nat → α)
    (same : ∀ j, offset≤j → j<offset+2^d → a j=b j) :
    Reduction.balanced d offset a=Reduction.balanced d offset b := by
  induction d generalizing offset with
  | zero => simp [Reduction.balanced,same offset (by omega) (by simp)]
  | succ d ih =>
    simp only [Reduction.balanced]
    congr 1
    · apply ih; intro j lo hi; apply same j lo
      rw [pow_succ] at *; omega
    · apply ih; intro j lo hi; apply same j (by omega)
      rw [pow_succ] at *; omega

/-- Dense specialization preserves the original instruction and memory model. -/
theorem output_iff (d : Nat) (p g : Fin (Sum.width d) → Word) (value : Word) :
    Dense.Output (Sum.shape d) (global d p g) 0 value ↔ Output d p g value := by
  have operands : Reduction.balanced d 0 (Dense.operands (Sum.shape d) (global d p g) 0) =
      Reduction.balanced d 0 (fun j => ((List.ofFn g)[j]!, (List.ofFn p)[j]!)) := by
    apply balanced_congr
    intro j _ hj
    have h : j<Sum.width d := by simpa [Sum.width] using hj
    simp only [Dense.operands,Sum.shape,h,ite_true,Dense.Shape.weight,
      Dense.Shape.weightBase,Nat.zero_mul,Nat.add_zero]
    exact Prod.ext (global_sensitivity_bang d p g j h) (global_probability_bang d p g j h)
  simp only [Dense.Output,Dense.Node,Sum.shape,Dense.activate,Bool.false_eq_true,ite_false,
    Nat.zero_mul]
  change (∃ dot affine, Reduction.Eval (Reduction.balanced d 0
      (Dense.operands (Sum.shape d) (global d p g) 0)) dot ∧
      Results .add dot (global d p g)[Sum.width d+1*Sum.width d+0]! affine ∧ value=affine) ↔ _
  rw [operands]
  have idx : Sum.width d+1*Sum.width d+0=2*Sum.width d := by omega
  rw [idx,global_bias]
  simp [Output]

/-- A launch retains an actual fetched, completed, memory-admitted execution. -/
abbrev Launch (d : Nat) (p g : Fin (Sum.width d) → Word) : List Word → Prop :=
  Dense.Launch (Sum.shape d) (global d p g)

/-- Every completed admitted launch changes only its output cell, and its stored
word satisfies the exact ordered arithmetic contract. -/
theorem launch_correct (d : Nat) (p g : Fin (Sum.width d) → Word) (run : Launch d p g after) :
    ∃ out, after=(global d p g).set (outputIndex d) out ∧ Output d p g out := by
  have result := Dense.launch_correct run
  obtain ⟨out,stored,allowed⟩ := result.1 ⟨0,by simp [Sum.shape]⟩
  have stored' : after[outputIndex d]?=some out := by simpa using stored
  refine ⟨out,?_,(output_iff d p g out).mp allowed⟩
  have size : (global d p g).length=outputIndex d+1 := by simp [outputIndex,Sum.outputIndex]
  apply List.ext_getElem?
  intro i
  by_cases same : i=outputIndex d
  · subst i
    simpa [size] using stored'
  · by_cases below : i<outputIndex d
    · rw [result.2.1 i (by simpa using below)]
      exact (List.getElem?_set_ne (Ne.symm same)).symm
    · have outside : after.length ≤ i := by rw [result.2.2,size]; omega
      have old : (global d p g).length ≤ i := by rw [size]; omega
      simp [List.getElem?_eq_none_iff.mpr outside,List.getElem?_eq_none_iff.mpr old,
        List.getElem?_set_ne (Ne.symm same)]

/-- Both operand arrays and the bias survive every completed admitted launch. -/
theorem launch_prefix (run : Launch d p g after) (i : Nat) (beforeOutput : i<outputIndex d) :
    after[i]?=(global d p g)[i]? :=
  (Dense.launch_correct run).2.1 i (by simpa using beforeOutput)

/-- Execution exists for all input bit patterns, independently of the finite
value restrictions used later for numerical accuracy. -/
theorem launch_exists (d : Nat) (bound : Sum.Bounds d) (p g : Fin (Sum.width d) → Word) :
    ∃ after, Launch d p g after :=
  Dense.launch_exists (Sum.shape d) (global d p g) (fun _ => Sum.denseBounds d bound) (by simp)

/-- The abstraction exposes the actual admitted trace and access safety for
every emitted global or shared load and store. -/
theorem launch_safe (launch : Launch d p g after) :
    ∃bound : Dense.Bounds (Sum.shape d), ∃seeds events final,
      ∃run : Runs (Dense.config (Sum.shape d) bound) (Sum.program d)
        (Dense.initial (Sum.shape d) (global d p g)
          (List.replicate (Sum.sharedWords d) 0) seeds) events final,
      after=final.global ∧ (∀t, (final.lanes t).halted=true) ∧
      (∃source co, Dense.Admitted (Sum.shape d) bound (global d p g)
        (List.replicate (Sum.sharedWords d) 0) seeds run source co) ∧
      (∀event∈events, AccessSafe (Dense.initial (Sum.shape d) (global d p g)
        (List.replicate (Sum.sharedWords d) 0) seeds) event) := by
  rw [← Sum.sharedWords_eq d]
  cases launch with
  | empty zero => simp [Sum.shape] at zero
  | kernel bound seeds run halted admitted =>
    exact ⟨bound,seeds,_,_,run,rfl,halted,admitted,runs_access_safe run⟩

end Ptx.Scalar.Parallel.SoftmaxBackwardDot
