import PtxBinary32.Normalize
import PtxBinary32.NormalizeProgram

/-! Numerical bounds tied to the operands and destination of the fetched
normalization program. No successful reciprocal is assumed as a premise. -/
namespace Ptx.Scalar.Normalize
open TorchLean.Floats (round32 eps32)

/-- Every actual run has the two rounded values and local error bounds of the
numerical contract. Finiteness is derived from the original input words. -/
theorem correct (target : Ptx.Target) (s t : Scalar.State)
    (numerator denominator destination : Nat) (u S : ℝ)
    (start : s.pc = 0) (scratch : destination ≠ numerator)
    (input : Ptx.Binary32.finiteReal (s.regs numerator) = some u)
    (sum : Ptx.Binary32.finiteReal (s.regs denominator) = some S)
    (small : |u| ≤ 2) (lower : 1/2 ≤ S)
    (run : Run target (program numerator denominator destination) s t) :
    Ptx.Binary32.finiteReal (t.regs destination) = some (round32 (u*round32 (1/S))) ∧
    |round32 (1/S)-1/S| ≤ eps32 (1/S) ∧
    |round32 (u*round32 (1/S))-u*round32 (1/S)| ≤ eps32 (u*round32 (1/S)) ∧
    |round32 (u*round32 (1/S))| ≤ 4 := by
  have stages := (run_results target s t numerator denominator destination start scratch run).1
  exact Ptx.Binary32.Normalize.correct _ _ _ u S input sum small lower stages

/-- A finite encoded result is attained by an actual fetched execution; the
reciprocal and product intermediate operands are not supplied by the caller. -/
theorem finite_execution_exists (target : Ptx.Target) (s : Scalar.State)
    (numerator denominator destination : Nat) (u S : ℝ)
    (supported : Scalar.Binary32.SupportedTarget target)
    (start : s.pc = 0) (scratch : destination ≠ numerator)
    (input : Ptx.Binary32.finiteReal (s.regs numerator) = some u)
    (sum : Ptx.Binary32.finiteReal (s.regs denominator) = some S)
    (small : |u| ≤ 2) (lower : 1/2 ≤ S) :
    ∃ t, Run target (program numerator denominator destination) s t ∧
      Ptx.Binary32.finiteReal (t.regs destination) = some (round32 (u*round32 (1/S))) ∧
      |round32 (u*round32 (1/S))| ≤ 4 := by
  obtain ⟨t,run⟩ := execution_exists target s numerator denominator destination supported start scratch
  have result := correct target s t numerator denominator destination u S start scratch input sum small lower run
  exact ⟨t,run,result.1,result.2.2.2⟩

end Ptx.Scalar.Normalize
