import PtxBinary32.SoftmaxPipeline

/-! Constructive whole-pipeline existence from initial scores. Every phase is
an actual fetched launch or pass. No total-error guard, desired intermediate
arithmetic value or successful reciprocal is assumed. -/
namespace Ptx.Scalar.SoftmaxPipeline
open Parallel SoftmaxStorage

private theorem supported : Scalar.Binary32.SupportedTarget target := by
  unfold Scalar.Binary32.SupportedTarget target
  decide

private theorem valid_index (d : Nat) (bound : Sum.Bounds d) (memory : List Word)
    (len : memory.length=2*Sum.width d+2) (i : Nat) (small : i≤Sum.outputIndex d) :
    SoftmaxMemory.ValidIndex memory i := by
  have cap : Sum.width d≤1024 := by simpa using (Sum.denseBounds d bound).threads
  unfold SoftmaxMemory.ValidIndex Sum.outputIndex at *
  constructor <;> omega

/-- Initial finite bounded scores suffice to construct the complete reference
pipeline, independently of the sufficient numerical-accuracy guard. -/
theorem execution_exists (d : Nat) (bound : Sum.Bounds d)
    (input : Fin (Sum.width d) → Word) (values : Fin (Sum.width d) → ℝ)
    (finite : ∀i, Ptx.Binary32.finiteReal (input i)=some (values i))
    (small : ∀i, |values i|≤(2:ℝ)^(124:ℤ)) : ∃final, Run d input final := by
  obtain ⟨maximum,maxRun⟩ := SoftmaxReductions.maximum_launch_exists d bound (Sum.global d input) (by change Sum.width d+1≤(Sum.global d input).length; simp; omega)
  have maxEq := SoftmaxReductions.maximum_launch_correct maxRun
  change maximum=(Sum.global d input).set (Sum.width d) (maximumWord d input) at maxEq
  have maxLen : maximum.length=2*Sum.width d+2 := by simp [maxEq]
  obtain ⟨m,maxValue,bounds,_⟩ := SoftmaxReductions.maximum_input_bounds d input values finite small
  have maxRead : maximum[Sum.width d]! = maximumWord d input := by
    rw [maxEq,List.getElem!_eq_getElem?_getD,List.getElem?_set_self (by simp; omega)]
    rfl
  have scores : ∀i : Fin (Sum.width d), maximum[i.val]! = input i := by
    intro i
    rw [maxEq,List.getElem!_eq_getElem?_getD,
      List.getElem?_set_ne (show Sum.width d≠i.val by have := i.isLt; omega),Sum.global_input]
    rfl
  obtain ⟨exponentials,expRun⟩ := SoftmaxSweep.exists_run (step:=exponentialStep d) maximum (Sum.width d) (by
    intro k hk middle prior
    have len : middle.length=2*Sum.width d+2 := (SoftmaxSweep.length (exponential_writes d) prior).trans maxLen
    have scoreRead : middle[k]! = input ⟨k,hk⟩ :=
      (bang_eq (SoftmaxSweep.outside (exponential_writes d) prior k le_rfl)).trans (scores ⟨k,hk⟩)
    have maximumRead : middle[Sum.width d]! = maximumWord d input :=
      (bang_eq (SoftmaxSweep.outside (exponential_writes d) prior _ (by omega))).trans maxRead
    have vk := valid_index d bound middle len k (by unfold Sum.outputIndex; omega)
    have vm := valid_index d bound middle len (Sum.width d) (by unfold Sum.outputIndex; omega)
    exact SoftmaxMemory.shifted_launch_exists target k (Sum.width d) k middle (values ⟨k,hk⟩) m
      supported vk vm vk (by rw [scoreRead]; exact finite ⟨k,hk⟩)
      (by rw [maximumRead]; exact maxValue) (bounds ⟨k,hk⟩))
  have expLen : exponentials.length=2*Sum.width d+2 :=
    (SoftmaxSweep.length (exponential_writes d) expRun).trans maxLen
  have restore := SoftmaxMemory.store_launch_exists target (Sum.width d) 0x3f800000 exponentials
    supported (valid_index d bound exponentials expLen _ (by unfold Sum.outputIndex; omega))
  have restoredEq : exponentials.set (Sum.width d) 0x3f800000 =
      Sum.global d (row (Sum.width d) exponentials) := by
    apply restore_weight d input (maximumWord d input) exponentials expLen
    intro i hi
    rw [← maxEq]
    exact SoftmaxSweep.outside (exponential_writes d) expRun i hi
  obtain ⟨summed,sumRun⟩ := SoftmaxReductions.sum_launch_exists d bound (row (Sum.width d) exponentials)
  have sumLen : summed.length=2*Sum.width d+2 := by
    simpa using (Dense.launch_correct sumRun).2.2
  obtain ⟨final,normRun⟩ := SoftmaxSweep.exists_run (step:=normalizationStep d) summed (Sum.width d) (by
    intro k hk middle prior
    have len : middle.length=2*Sum.width d+2 :=
      (SoftmaxSweep.length (normalization_writes d) prior).trans sumLen
    have vk := valid_index d bound middle len k (by unfold Sum.outputIndex; omega)
    exact SoftmaxMemory.normalize_launch_exists target k (Sum.outputIndex d) k middle
      supported vk (valid_index d bound middle len _ le_rfl) vk)
  exact ⟨final,.phases maxRun expRun restore (by simpa only [restoredEq] using sumRun) normRun⟩

end Ptx.Scalar.SoftmaxPipeline
