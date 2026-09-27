import PtxBinary32.ShiftedExpProgram
import PtxBinary32.ExponentialChecks

/-! Boundary obligations for the four-step sequence, not hardware runs. -/
namespace Ptx.Scalar.ShiftedExp.Checks
open Ptx.Binary32
open FloatLib.Floats.Formats.BinaryInterchange (Model FloatFormat)
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics

/-- The sequence really uses explicit rounded arithmetic and non-FTZ ex2. -/
theorem spellings : (text 0 1 2).map (·.mnemonic) =
    ["mul.rn.f32", "add.rn.f32", "mul.rn.f32", "ex2.approx.f32"] := by decide

/-- Absence of fetch is not replaced by numerical correctness. -/
theorem missing_fetch (target : Ptx.Target) (s t : Scalar.State) :
    ¬ Run target [] s t := by
  rintro ⟨_,_,_,_,_,_,_,⟨_,i,fetch,_⟩,_⟩
  simp at fetch

theorem unsupported_target (target : Ptx.Target) (p : List Instr) (s t : Scalar.State)
    (unsupported : ¬ Scalar.Binary32.SupportedTarget target) : ¬ Run target p s t := by
  rintro ⟨_,_,_,_,_,_,_,⟨supported,_⟩,_⟩
  exact unsupported supported

/-- The scratch register can replace the supplied maximum after its first read. -/
theorem maximum_alias (s : Scalar.State) (x m : ℝ) (start : s.pc = 0)
    (inputValue : finiteReal (s.regs 0) = some x)
    (maximumValue : finiteReal (s.regs 1) = some m)
    (bounds : Ptx.Binary32.ShiftedExp.InputBounds x m) :
    ∃ t, Run ⟨94,20⟩ (program 0 1 1) s t :=
  execution_exists _ s 0 1 1 x m (by norm_num [Scalar.Binary32.SupportedTarget]) start (by decide) inputValue maximumValue bounds

/-- The lowest-magnitude negative value survives the negate/add shift; FTZ
would turn this nonzero shifted result into zero. -/
theorem subnormal_shift :
    Ptx.Binary32.Results .mul 0 0xbf800000 0x80000000 ∧
    Ptx.Binary32.Results .add 0x80000001 0x80000000 0x80000001 := by
  constructor <;> unfold Ptx.Binary32.Results <;> decide

/-- Inclusive magnitude boundaries include opposite signs, so overflow safety
is not only checked on small positive examples. -/
theorem endpoint_real : finiteReal (0x7d800000 : Word) = some ((2:ℝ)^(124:ℤ)) ∧
    finiteReal (0xfd800000 : Word) = some (-(2:ℝ)^(124:ℤ)) := by
  constructor
  · rw [finiteReal_some _ (by decide)]
    change some (Model.toReal (Model.ofFields FloatFormat.binary32 false 251 0)) = _
    rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
    norm_num [FloatFormat.binary32,Model.pow2,bpow,binaryRadix,Radix.toReal]
  · rw [finiteReal_some _ (by decide)]
    change some (Model.toReal (Model.ofFields FloatFormat.binary32 true 251 0)) = _
    rw [Model.toReal_ofFields_normal _ _ _ _ (by decide) (by decide) (by decide)]
    norm_num [FloatFormat.binary32,Model.pow2,bpow,binaryRadix,Radix.toReal]

theorem endpoint_stages : ∃ negative shifted product output,
    Ptx.Binary32.Results .mul 0x7d800000 0xbf800000 negative ∧
    Ptx.Binary32.Results .add 0xfd800000 negative shifted ∧
    Ptx.Binary32.Results .mul shifted ExpArgument.constantWord product ∧
    Exponential.Results product output := by
  apply Ptx.Binary32.ShiftedExp.stages_exist _ _ _ _ endpoint_real.2 endpoint_real.1
  norm_num [Ptx.Binary32.ShiftedExp.InputBounds]

private def initial (x m : Word) : Scalar.State :=
  ⟨0, (fun r => if r = 0 then x else if r = 1 then m else 0xdeadbeef),
    (fun _ => 7), (fun _ => true), [0x12345678]⟩

/-- Mixed zero signs, destructive reuse of the maximum register, exact one,
and unchanged input and memory hold together for an actual admitted run. -/
theorem signed_zero_execution : ∃ t,
    Run ⟨94,20⟩ (program 0 1 1) (initial 0x80000000 0) t ∧
    t.regs 1 = 0x3f800000 ∧ t.regs 0 = 0x80000000 ∧ t.memory = [0x12345678] := by
  have left : finiteReal ((initial 0x80000000 0).regs 0) = some 0 := by
    simpa [initial] using Ptx.Binary32.Exponential.Checks.negative_zero_real
  have right : finiteReal ((initial 0x80000000 0).regs 1) = some 0 := by
    simpa [initial] using Ptx.Binary32.Exponential.Checks.positive_zero_real
  obtain ⟨t,run⟩ := maximum_alias (initial 0x80000000 0) 0 0 rfl left right
    (by norm_num [Ptx.Binary32.ShiftedExp.InputBounds])
  have one := maximal_score _ _ t 0 1 1 0 rfl (by decide) left right (by norm_num) run
  have frame := (run_results _ _ t 0 1 1 rfl (by decide) run).2
  exact ⟨t,run,one,frame.2.2.2.2 0 (by decide),frame.2.1⟩

/-- A genuinely negative shifted score has both an execution witness and an
all-result bound around exp(-1); the exponential is not chosen by the test. -/
theorem negative_shift_execution : ∃ t,
    Run ⟨94,20⟩ (program 0 1 2) (initial 0 0x3f800000) t ∧
    ∃ u, finiteReal (t.regs 2) = some u ∧
      |u-Real.exp (0-1)| ≤ 5/(2:ℝ)^24 + Real.log 2 *
        ExpArgument.budget (TorchLean.Floats.round32 (0-1)) (TorchLean.Floats.eps32 (0-1)) := by
  have left : finiteReal ((initial 0 0x3f800000).regs 0) = some 0 := by
    simpa [initial] using Ptx.Binary32.Exponential.Checks.positive_zero_real
  have right : finiteReal ((initial 0 0x3f800000).regs 1) = some 1 := by
    simpa [initial] using Bounds.positive_one_real
  have bounds : Ptx.Binary32.ShiftedExp.InputBounds 0 1 := by
    norm_num [Ptx.Binary32.ShiftedExp.InputBounds]
  obtain ⟨t,run⟩ := execution_exists ⟨94,20⟩ _ 0 1 2 0 1
    (by norm_num [Scalar.Binary32.SupportedTarget]) rfl (by decide) left right bounds
  exact ⟨t,run,correct _ _ t 0 1 2 0 1 rfl (by decide) left right bounds run⟩

end Ptx.Scalar.ShiftedExp.Checks
