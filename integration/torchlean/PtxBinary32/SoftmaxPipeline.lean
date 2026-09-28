import PtxBinary32.SoftmaxMemory
import PtxBinary32.SoftmaxReductions
import PtxBinary32.SoftmaxStorage
import PtxBinary32.SoftmaxForwardAccuracy

/-! A same-arena reference pipeline. Parallel reductions are separated by
sequential fetched load/arithmetic/store passes. Phase boundaries reset entry
state and wait in the composition model; they are not CUDA runtime code. -/
namespace Ptx.Scalar.SoftmaxPipeline
open Parallel SoftmaxStorage
open Ptx.Binary32

def target : Target := ⟨94,70⟩

def exponentialStep (d i : Nat) : List Word → List Word → Prop :=
  SoftmaxMemory.ShiftLaunch target i (Sum.width d) i

def normalizationStep (d i : Nat) : List Word → List Word → Prop :=
  SoftmaxMemory.NormalizeLaunch target i (Sum.outputIndex d) i

/-- The sum launch consumes the restored arena itself, not a separately supplied
vector of desired exponential values. Every phase writes back its actual memory. -/
inductive Run (d : Nat) (input : Fin (Sum.width d) → Word) : List Word → Prop
  | phases {maximum exponentials restored summed final : List Word}
      (maxRun : SoftmaxReductions.MaximumLaunch d (Sum.global d input) maximum)
      (expRun : SoftmaxSweep.Run (exponentialStep d) (Sum.width d) maximum exponentials)
      (restore : SoftmaxMemory.StoreLaunch target (Sum.width d) 0x3f800000 exponentials restored)
      (sumRun : Dense.Launch (Sum.shape d) restored summed)
      (normRun : SoftmaxSweep.Run (normalizationStep d) (Sum.width d) summed final) :
      Run d input final

def maximumWord (d : Nat) (input : Fin (Sum.width d) → Word) : Word :=
  Maximum.node (Sum.global d input) d 0

theorem exponential_writes (d : Nat) : SoftmaxSweep.WritesOwn (exponentialStep d) := by
  intro i a b run
  obtain ⟨value,_,eq⟩ := SoftmaxMemory.shifted_launch_correct run
  exact ⟨value,eq⟩

theorem normalization_writes (d : Nat) : SoftmaxSweep.WritesOwn (normalizationStep d) := by
  intro i a b run
  obtain ⟨value,_,eq⟩ := SoftmaxMemory.normalize_launch_correct run
  exact ⟨value,eq⟩

/-- Exact arithmetic relations are extracted from the original scores and final
stored outputs. No computed intermediate values are assumed at phase boundaries. -/
theorem arithmetic (run : Run d input final) :
    ∃ exponential : Fin (Sum.width d) → Word, ∃ denominator,
      (∀i, SoftmaxForward.ExpStages (input i) (maximumWord d input) (exponential i)) ∧
      Sum.Output d exponential denominator ∧
      (∀i, Binary32.Normalize.Stages (exponential i) denominator (final[i.val]!)) ∧
      final.length=2*Sum.width d+2 := by
  cases run with
  | @phases maximum exponentials restored summed final maxRun expRun restore sumRun normRun =>
    have maxEq := SoftmaxReductions.maximum_launch_correct maxRun
    change maximum=(Sum.global d input).set (Sum.width d) (maximumWord d input) at maxEq
    have maxLen : maximum.length=2*Sum.width d+2 := by simp [maxEq]
    have expLen : exponentials.length=2*Sum.width d+2 :=
      (SoftmaxSweep.length (exponential_writes d) expRun).trans maxLen
    have expRel := pass_relations (fun i a b h => SoftmaxMemory.shifted_launch_correct h)
      expRun (by omega) (show Sum.width d ≤ Sum.width d from le_rfl)
    have restoredEq : restored=Sum.global d (row (Sum.width d) exponentials) := by
      rw [SoftmaxMemory.store_launch_correct restore]
      apply restore_weight d input (maximumWord d input) exponentials expLen
      intro i hi
      rw [← maxEq]
      exact SoftmaxSweep.outside (exponential_writes d) expRun i hi
    have sumLaunch : SoftmaxReductions.SumLaunch d (row (Sum.width d) exponentials) summed := by
      simpa only [restoredEq] using sumRun
    obtain ⟨den,sumEq,sumAllowed⟩ := SoftmaxReductions.sum_launch_correct d _ sumLaunch
    have sumLen : summed.length=2*Sum.width d+2 := by simp [sumEq]
    have normRel := pass_relations (fun i a b h => SoftmaxMemory.normalize_launch_correct h)
      normRun (by omega) (show Sum.width d ≤ Sum.outputIndex d by unfold Sum.outputIndex; omega)
    refine ⟨row (Sum.width d) exponentials,den,?_,sumAllowed,?_,
      (SoftmaxSweep.length (normalization_writes d) normRun).trans sumLen⟩
    · intro i
      have h := expRel i
      have score : maximum[i.val]! = input i := by
        have ne : Sum.width d ≠ i.val := by have := i.isLt; omega
        simp only [maxEq,List.getElem!_eq_getElem?_getD,List.getElem?_set_ne ne,
          Sum.global_input,Option.getD_some]
      have maxValue : maximum[Sum.width d]! = maximumWord d input := by
        have inside : Sum.width d<(Sum.global d input).length := by rw [Sum.global_length]; omega
        simp only [maxEq,List.getElem!_eq_getElem?_getD,List.getElem?_set_self inside,
          Option.getD_some]
      simpa only [score,maxValue,SoftmaxMemory.ShiftedStages,SoftmaxForward.ExpStages,row] using h
    · intro i
      have h := normRel i
      have numerator : summed[i.val]! = row (Sum.width d) exponentials i := by
        have ne : Sum.outputIndex d ≠ i.val := by have := i.isLt; unfold Sum.outputIndex; omega
        simp only [sumEq,List.getElem!_eq_getElem?_getD,List.getElem?_set_ne ne,
          Sum.global_input,Option.getD_some]
      have denominator : summed[Sum.outputIndex d]! = den := by
        simp [sumEq,Sum.outputIndex]
      simpa only [numerator,denominator,SoftmaxMemory.NormalizeStages,Binary32.Normalize.Stages] using h

end Ptx.Scalar.SoftmaxPipeline
