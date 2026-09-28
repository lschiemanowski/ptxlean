import PtxBinary32.UnaryPointwiseLaunch
import PtxBinary32.UnarySequential
import PtxBinary32.SoftmaxPipelineExists

/-! Parallel elementwise passes replace the sequential reference passes. Their
complete admitted executions refine the reference output relation; this does
not impose a sequential schedule on the parallel program. Reduction and phase
boundaries retain their existing explicit model-level meaning. -/
namespace Ptx.Scalar.SoftmaxParallel
open Parallel

inductive Run (d : Nat) (input : Fin (Sum.width d) → Word) : List Word → Prop
  | phases {maximum exponentials restored summed final : List Word}
      (maxRun : SoftmaxReductions.MaximumLaunch d (Sum.global d input) maximum)
      (expRun : UnaryPointwise.Launch .shifted (Sum.width d) (Sum.width d) maximum exponentials)
      (restore : SoftmaxMemory.StoreLaunch SoftmaxPipeline.target (Sum.width d) 0x3f800000 exponentials restored)
      (sumRun : Dense.Launch (Sum.shape d) restored summed)
      (normRun : UnaryPointwise.Launch .normalize (Sum.width d) (Sum.outputIndex d) summed final) :
      Run d input final

/-- Every admitted parallel output is a possible reference output. Only final
array results are related; the actual parallel trace and scheduling stay free. -/
theorem refines (run : Run d input final) : SoftmaxPipeline.Run d input final := by
  cases run with
  | phases maxRun expRun restore sumRun normRun =>
    exact .phases maxRun
      (UnaryPointwise.sequential_realize _ _ _ _ _ (UnaryPointwise.launch_bounds expRun)
        (UnaryPointwise.launch_spec expRun))
      restore sumRun
      (UnaryPointwise.sequential_realize _ _ _ _ _ (UnaryPointwise.launch_bounds normRun)
        (UnaryPointwise.launch_spec normRun))

private theorem pass_bounds (d : Nat) (bound : Sum.Bounds d) (memory : List Word)
    (len : memory.length=2*Sum.width d+2) (common : Nat)
    (low : Sum.width d≤common) (high : common≤Sum.outputIndex d) :
    UnaryPointwise.Bounds (Sum.width d) common memory := by
  have cap : Sum.width d≤1024 := by simpa using (Sum.denseBounds d bound).threads
  refine ⟨Nat.two_pow_pos d,cap,low,?_,?_⟩
  · rw [len]; unfold Sum.outputIndex at high; omega
  · rw [len]; omega

/-- Every reference result can also be obtained by a concrete, admitted parallel
execution. Arithmetic nondeterminism is preserved in both directions. -/
theorem of_reference (bound : Sum.Bounds d) (run : SoftmaxPipeline.Run d input final) :
    Run d input final := by
  cases run with
  | @phases maximum exponentials restored summed final maxRun expRun restore sumRun normRun =>
    have maxEq := SoftmaxReductions.maximum_launch_correct maxRun
    have maxLen : maximum.length=2*Sum.width d+2 := by simp [maxEq]
    have expLen : exponentials.length=2*Sum.width d+2 :=
      (SoftmaxSweep.length (SoftmaxPipeline.exponential_writes d) expRun).trans maxLen
    have restoreLen : restored.length=2*Sum.width d+2 := by
      rw [SoftmaxMemory.store_launch_correct restore,List.length_set]; exact expLen
    have sumLen : summed.length=2*Sum.width d+2 := (Dense.launch_correct sumRun).2.2.trans restoreLen
    have expBounds := pass_bounds d bound maximum maxLen (Sum.width d) le_rfl (by unfold Sum.outputIndex; omega)
    have normBounds := pass_bounds d bound summed sumLen (Sum.outputIndex d) (by unfold Sum.outputIndex; omega) le_rfl
    exact .phases maxRun
      (UnaryPointwise.launch_realize _ _ _ _ _ expBounds
        (UnaryPointwise.sequential_spec _ _ _ _ _ expBounds expRun))
      restore sumRun
      (UnaryPointwise.launch_realize _ _ _ _ _ normBounds
        (UnaryPointwise.sequential_spec _ _ _ _ _ normBounds normRun))

theorem output_equivalence (bound : Sum.Bounds d) :
    Run d input final ↔ SoftmaxPipeline.Run d input final :=
  ⟨refines,of_reference bound⟩

/-- No successful intermediate or final output is supplied as a premise. -/
theorem execution_exists (d : Nat) (bound : Sum.Bounds d)
    (input : Fin (Sum.width d) → Word) (values : Fin (Sum.width d) → ℝ)
    (finite : ∀i, Ptx.Binary32.finiteReal (input i)=some (values i))
    (small : ∀i, |values i|≤(2:ℝ)^(124:ℤ)) : ∃final, Run d input final := by
  obtain ⟨final,run⟩ := SoftmaxPipeline.execution_exists d bound input values finite small
  exact ⟨final,of_reference bound run⟩

end Ptx.Scalar.SoftmaxParallel
