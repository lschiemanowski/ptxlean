import PtxBinary32.SoftmaxParallel
import PtxBinary32.SoftmaxBackward

/-! A complete memory-connected forward/backward composition. Releasing forward
scratch retains the actual output prefix, then supplies the incoming row and
fresh backward scratch. No host operation computes gradient arithmetic. -/
namespace Ptx.Scalar.Parallel.SoftmaxBackward

inductive FullRun (d : Nat) (bound : Sum.Bounds d)
    (input incoming : Fin (Sum.width d) → Word) : List Word → Prop
  | phases {forward final : List Word}
      (forwardRun : Scalar.SoftmaxParallel.Run d input forward)
      (backwardRun : Run d bound (SoftmaxStorage.row (Sum.width d) forward) incoming final) :
      FullRun d bound input incoming final

/-- The backward entry arena retains exactly the produced prefix. Its new row
is supplied external input; the two remaining words are freshly allocated. -/
theorem entry_is_storage_view (run : Scalar.SoftmaxParallel.Run d input forward)
    (incoming : Fin (Sum.width d) → Word) :
    SoftmaxBackwardDot.global d (SoftmaxStorage.row (Sum.width d) forward) incoming =
      forward.take (Sum.width d) ++ List.ofFn incoming ++ [0,0] := by
  obtain ⟨_,_,_,_,_,len⟩ := Scalar.SoftmaxPipeline.arithmetic (Scalar.SoftmaxParallel.refines run)
  rw [SoftmaxBackwardDot.global,row_is_prefix _ _ (by omega)]

/-- Backward is operationally total on words. The forward's original-score
conditions suffice for whole-composition existence, independently of accuracy. -/
theorem full_execution_exists (d : Nat) (bound : Sum.Bounds d)
    (input incoming : Fin (Sum.width d) → Word) (values : Fin (Sum.width d) → ℝ)
    (finite : ∀i,Ptx.Binary32.finiteReal (input i)=some (values i))
    (small : ∀i,|values i|≤(2:ℝ)^(124:ℤ)) :
    ∃final,FullRun d bound input incoming final := by
  obtain ⟨forward,frun⟩ := Scalar.SoftmaxParallel.execution_exists d bound input values finite small
  obtain ⟨final,brun⟩ := execution_exists d bound (SoftmaxStorage.row (Sum.width d) forward) incoming
  exact ⟨final,.phases frun brun⟩

end Ptx.Scalar.Parallel.SoftmaxBackward
