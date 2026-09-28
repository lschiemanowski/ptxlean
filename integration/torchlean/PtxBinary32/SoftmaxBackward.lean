import PtxBinary32.SoftmaxBackwardLayout
import PtxBinary32.SoftmaxBackwardDot

/-! Three separate completed launches implement a backward row. Only fresh
scratch suffixes are allocated between phases; every arithmetic result comes
from a fetched instruction and an admitted memory execution. -/
namespace Ptx.Scalar.Parallel.SoftmaxBackward
open Ptx.Binary32

inductive Run (d : Nat) (bound : Sum.Bounds d) (p g : Fin (Sum.width d) → Word) : List Word → Prop
  | phases {dot differences final : List Word}
      (dotRun : SoftmaxBackwardDot.Launch d p g dot)
      (differenceRun : Pointwise.Launch .difference (differenceLayout d bound) (extend d dot) differences)
      (gradientRun : Pointwise.Launch .mul (gradientLayout d bound) (extend d differences) final) :
      Run d bound p g final

/-- The final array retains both original rows and the actual dot and difference
scratch words. The returned gradient is computed from the stored forward word. -/
theorem correct (run : Run d bound p g final) :
    final.length=4*Sum.width d+2 ∧
    (∀i : Fin (Sum.width d), final[i.val]?=some (p i) ∧
      final[Sum.width d+i.val]?=some (g i)) ∧
    ∃q, SoftmaxBackwardDot.Output d p g q ∧
      final[Sum.outputIndex d]?=some q ∧
      ∀i : Fin (Sum.width d), ∃negative difference,
        Results .mul q 0xbf800000 negative ∧
        Results .add (g i) negative difference ∧
        final[differenceBase d+i.val]?=some difference ∧
        Results .mul (p i) difference final[gradientBase d+i.val]! := by
  cases run with
  | @phases dot differences final dotRun differenceRun gradientRun =>
    obtain ⟨q,dotEq,qResult⟩ := SoftmaxBackwardDot.launch_correct d p g dotRun
    have dc := Pointwise.launch_correct differenceRun
    have gc := Pointwise.launch_correct gradientRun
    have dotSize : _ := congrArg List.length dotEq
    simp only [List.length_set,SoftmaxBackwardDot.global_length] at dotSize
    have diffSize := dc.2.2
    have finalSize := gc.2.2
    rw [extend_length,dotSize] at diffSize
    rw [extend_length,diffSize] at finalSize
    have dotPrefix (j : Nat) (hj : j<Sum.outputIndex d) :
        _ := SoftmaxBackwardDot.launch_prefix dotRun j hj
    have diffPrefix (j : Nat) (hj : j<differenceBase d) :
        _ := dc.2.1 j hj
    have finalPrefix (j : Nat) (hj : j<gradientBase d) :
        _ := gc.2.1 j hj
    have dotInside : Sum.outputIndex d < dot.length := by
      rw [dotSize]; unfold Sum.outputIndex; omega
    have qSaved : dot[Sum.outputIndex d]?=some q := by
      rw [dotEq]
      simp [SoftmaxBackwardDot.outputIndex,Sum.outputIndex]
    have retain (j : Nat) (hj : j<differenceBase d) :
        final[j]? = dot[j]? := by
      rw [finalPrefix j (by unfold differenceBase gradientBase at *; omega),
        extend_prefix _ _ _ (by rw [diffSize]; unfold differenceBase at hj; omega),
        diffPrefix j hj,extend_prefix _ _ _ (by rw [dotSize]; exact hj)]
    refine ⟨by omega,?_,q,qResult,?_,?_⟩
    · intro i
      constructor
      · rw [retain _ (by have := i.isLt; unfold differenceBase; omega),
          dotPrefix _ (by have := i.isLt; unfold Sum.outputIndex; omega)]
        exact SoftmaxBackwardDot.global_probability d p g i
      · rw [retain _ (by have := i.isLt; unfold differenceBase; omega),
          dotPrefix _ (by have := i.isLt; unfold Sum.outputIndex; omega)]
        exact SoftmaxBackwardDot.global_sensitivity d p g i
    · rw [retain _ (by unfold differenceBase Sum.outputIndex; omega)]
      exact qSaved
    · intro i
      obtain ⟨difference,storedDifference,allowedDifference⟩ := dc.1 i
      have left : (extend d dot)[Sum.width d+i.val]! =(g i) := by
        apply saved_word
        rw [extend_prefix _ _ _ (by rw [dotSize]; have := i.isLt; omega),
          dotPrefix _ (by have := i.isLt; unfold Sum.outputIndex; omega)]
        exact SoftmaxBackwardDot.global_sensitivity d p g i
      have right : (extend d dot)[Sum.outputIndex d]! =q := by
        apply saved_word
        rw [extend_prefix _ _ _ dotInside]
        exact qSaved
      change Pointwise.Result .difference (extend d dot)[Sum.width d+i.val]! (extend d dot)[Sum.outputIndex d]! difference at allowedDifference
      rw [left,right] at allowedDifference
      obtain ⟨negative,negativeAllowed,differenceAllowed⟩ := allowedDifference
      have differenceSaved : final[differenceBase d+i.val]?=some difference := by
        rw [finalPrefix _ (by have := i.isLt; unfold differenceBase gradientBase; omega),
          extend_prefix _ _ _ (by rw [diffSize]; have := i.isLt; unfold differenceBase; omega)]
        exact storedDifference
      obtain ⟨value,storedValue,allowedValue⟩ := gc.1 i
      have gradientLeft : (extend d differences)[i.val]! =(p i) := by
        apply saved_word
        rw [extend_prefix _ _ _ (by rw [diffSize]; have := i.isLt; omega),
          diffPrefix _ (by have := i.isLt; unfold differenceBase; omega),
          extend_prefix _ _ _ (by rw [dotSize]; have := i.isLt; omega),
          dotPrefix _ (by have := i.isLt; unfold Sum.outputIndex; omega)]
        exact SoftmaxBackwardDot.global_probability d p g i
      have gradientRight : (extend d differences)[differenceBase d+i.val]! =difference := by
        apply saved_word
        rw [extend_prefix _ _ _ (by rw [diffSize]; have := i.isLt; unfold differenceBase; omega)]
        exact storedDifference
      change Results .mul (extend d differences)[i.val]! (extend d differences)[differenceBase d+i.val]! value at allowedValue
      rw [gradientLeft,gradientRight] at allowedValue
      refine ⟨negative,difference,negativeAllowed,differenceAllowed,differenceSaved,?_⟩
      change final[gradientBase d+i.val]?=some value at storedValue
      rw [saved_word _ _ _ storedValue]
      exact allowedValue

/-- A completed admitted execution exists for all input words; finite inputs
are needed for the accuracy theorem, not to populate this execution relation. -/
theorem execution_exists (d : Nat) (bound : Sum.Bounds d) (p g : Fin (Sum.width d) → Word) :
    ∃final, Run d bound p g final := by
  obtain ⟨dot,dotRun⟩ := SoftmaxBackwardDot.launch_exists d bound p g
  have dotSize := (Dense.launch_correct dotRun).2.2
  simp only [SoftmaxBackwardDot.global_length] at dotSize
  obtain ⟨differences,differenceRun⟩ := Pointwise.launch_exists .difference (differenceLayout d bound)
    (extend d dot) (width_bound d bound) (by simp [differenceLayout,differenceBase,dotSize])
  have diffSize := (Pointwise.launch_correct differenceRun).2.2
  rw [extend_length,dotSize] at diffSize
  obtain ⟨final,gradientRun⟩ := Pointwise.launch_exists .mul (gradientLayout d bound)
    (extend d differences) (width_bound d bound) (by simp [gradientLayout,gradientBase,diffSize]; omega)
  exact ⟨final,.phases dotRun differenceRun gradientRun⟩

/-- A safety certificate names the fetched program and initial state and retains
its actual completed trace. It does not quantify over hypothetical accesses. -/
def TraceSafe (cfg : Config n) (code : List Instr) (initial : State n) (after : List Word) : Prop :=
  ∃events final, Runs cfg code initial events final ∧ after=final.global ∧
    (∀t, (final.lanes t).halted=true) ∧ ∀event∈events, AccessSafe initial event

def PointwiseSafe (op : Pointwise.Op) (l : Pointwise.Layout n) (before after : List Word) : Prop :=
  ∃positive : 0<n, ∃seeds,
    TraceSafe (Pointwise.config positive) (Pointwise.program op) (Pointwise.initial l before [] seeds) after

private theorem pointwise_safe {l : Pointwise.Layout n} (positive : 0<n) (run : Pointwise.Launch op l before after) :
    PointwiseSafe op l before after := by
  cases run with
  | empty zero => omega
  | kernel pos resource seeds actual halted admitted =>
    exact ⟨pos,seeds,_,_,actual,rfl,halted,runs_access_safe actual⟩

/-- All three phases retain completed actual traces whose emitted accesses are
safe. Phase boundaries allocate scratch suffixes and wait for completion. -/
theorem access_safe (run : Run d bound p g final) :
    ∃dot differences, SoftmaxBackwardDot.Launch d p g dot ∧
      (∃denseBound : Dense.Bounds (Sum.shape d), ∃seeds,
        TraceSafe (Dense.config (Sum.shape d) denseBound) (Sum.program d)
          (Dense.initial (Sum.shape d) (SoftmaxBackwardDot.global d p g)
            (List.replicate (Sum.sharedWords d) 0) seeds) dot) ∧
      Pointwise.Launch .difference (differenceLayout d bound) (extend d dot) differences ∧
      PointwiseSafe .difference (differenceLayout d bound) (extend d dot) differences ∧
      Pointwise.Launch .mul (gradientLayout d bound) (extend d differences) final ∧
      PointwiseSafe .mul (gradientLayout d bound) (extend d differences) final := by
  cases run with
  | phases dotRun differenceRun gradientRun =>
    obtain ⟨denseBound,seeds,events,state,actual,same,halted,admitted,safe⟩ :=
      SoftmaxBackwardDot.launch_safe dotRun
    have positive : 0<Sum.width d := by unfold Sum.width; positivity
    exact ⟨_,_,dotRun,⟨denseBound,seeds,events,state,actual,same,halted,safe⟩,
      differenceRun,pointwise_safe positive differenceRun,gradientRun,pointwise_safe positive gradientRun⟩

end Ptx.Scalar.Parallel.SoftmaxBackward
