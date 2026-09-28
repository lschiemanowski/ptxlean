import PtxBinary32.SoftmaxBackwardFull
import PtxBinary32.SoftmaxBackwardDotCorrect
import PtxBinary32.SoftmaxBackwardNumeric
import PtxBinary32.SoftmaxParallelChecks

/-! End-to-end regression: every completed singleton forward/backward execution
has zero real gradient, independently of the finite score and sensitivity.
Existence is proved separately, so the universal result is not vacuous. -/
namespace Ptx.Scalar.Parallel.SoftmaxBackward.Checks
set_option maxHeartbeats 200000
open Ptx.Binary32
open TorchLean.Floats (round32)
local instance : NeZero (Sum.width 0) := ⟨by norm_num [Sum.width]⟩

private theorem index_zero (i : Fin (Sum.width 0)) : i=0 := by
  apply Fin.ext
  have := i.isLt
  simp only [Sum.width,pow_zero] at this
  norm_num [Sum.width] at *
  omega

/-- This is real-value equality, not a claim about the sign bit of stored zero. -/
theorem singleton_exact (bound : Sum.Bounds 0)
    (input incoming : Fin (Sum.width 0) → Word) (x g : ℝ)
    (inputFinite : finiteReal (input 0)=some x) (inputSmall : |x|≤(2:ℝ)^(124:ℤ))
    (incomingFinite : finiteReal (incoming 0)=some g) (incomingSmall : |g|≤(2:ℝ)^60)
    (run : FullRun 0 bound input incoming final) :
    finiteReal final[gradientBase 0]! =some 0 := by
  cases run with
  | @phases forward final forwardRun backwardRun =>
    have one := Scalar.SoftmaxParallel.Checks.singleton_exact input x inputFinite inputSmall forwardRun
    let p := SoftmaxStorage.row (Sum.width 0) forward
    have pOne : p 0=0x3f800000 := by
      change forward[0]! =_
      exact saved_word _ _ _ one
    have pFinite : ∀i,finiteReal (p i)=some (1:ℝ) := by
      intro i
      rw [index_zero i,pOne]
      exact Bounds.positive_one_real
    have gFinite : ∀i,finiteReal (incoming i)=some g := by
      intro i
      rw [index_zero i]
      exact incomingFinite
    obtain ⟨_,_,q,qAllowed,_,coordinate⟩ := correct backwardRun
    have qAccuracy := SoftmaxBackwardDot.output_accuracy 0 bound p incoming
      (fun _ => (1:ℝ)) (fun _ => g) q pFinite gFinite (by intro i; norm_num)
      (fun _ => incomingSmall) qAllowed
    have rounded : BackwardDot.vector_rounded 0 (fun _ => g) (fun _ => (1:ℝ))=g := by
      simp [BackwardDot.vector_rounded,BackwardDot.rounded,BackwardDot.valuesAt,
        BackwardDot.finite_fixed _ _ incomingFinite]
    have qFinite : finiteReal q=some g := by
      exact qAccuracy.1.trans (congrArg some rounded)
    obtain ⟨negative,difference,hn,hd,_,ho⟩ := coordinate 0
    have h := SoftmaxBackwardNumeric.stages (p 0) (incoming 0) q negative difference
      final[gradientBase 0+0]! 1 g g (pFinite 0) incomingFinite qFinite
      (by norm_num) incomingSmall (incomingSmall.trans (by norm_num)) hn hd ho
    have zero : SoftmaxBackwardNumeric.gradient 1 g g=0 := by
      simp only [SoftmaxBackwardNumeric.gradient,SoftmaxBackwardNumeric.difference,sub_self]
      have rz : round32 0=0 := FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_zero .binary32
      rw [rz,mul_zero,rz]
    simpa [zero] using h.2.2.1

/-- An actual complete forward/backward execution exists and has the same zero
result for every finite score and bounded finite incoming sensitivity. -/
theorem singleton_exists (bound : Sum.Bounds 0)
    (input incoming : Fin (Sum.width 0) → Word) (x g : ℝ)
    (inputFinite : finiteReal (input 0)=some x) (inputSmall : |x|≤(2:ℝ)^(124:ℤ))
    (incomingFinite : finiteReal (incoming 0)=some g) (incomingSmall : |g|≤(2:ℝ)^60) :
    ∃final, FullRun 0 bound input incoming final ∧ finiteReal final[gradientBase 0]! =some 0 := by
  obtain ⟨final,run⟩ := full_execution_exists 0 bound input incoming (fun _ => x)
    (by intro i; rw [index_zero i]; exact inputFinite) (fun _ => inputSmall)
  exact ⟨final,run,singleton_exact bound input incoming x g inputFinite inputSmall
    incomingFinite incomingSmall run⟩

end Ptx.Scalar.Parallel.SoftmaxBackward.Checks
