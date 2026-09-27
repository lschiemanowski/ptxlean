import PtxBinary32.Reciprocal

/-! Encoded reciprocal edge cases, checked by the Lean kernel. These are
arithmetic tests, not a PTX decoder or hardware experiment. -/
namespace Ptx.Binary32.Reciprocal.Checks

theorem signed_zeros : reference 0 = 0x7f800000 ∧ reference 0x80000000 = 0xff800000 := by
  decide

theorem signed_infinities : reference 0x7f800000 = 0 ∧ reference 0xff800000 = 0x80000000 := by
  decide

theorem signs : reference 0x40000000 = 0x3f000000 ∧ reference 0xc0000000 = 0xbf000000 := by
  decide

/-- One third is rounded, not confused with integer division. -/
theorem rounded_third : reference 0x40400000 = 0x3eaaaaab := by decide

/-- Gradual underflow preserves the finite reciprocal of the largest input. -/
theorem subnormal_output : reference 0x7f7fffff = 0x00200000 := by decide

theorem overflow_from_subnormal : reference 1 = 0x7f800000 := by decide

theorem nan_freedom : Results 0x7fc00000 0x7fc00001 ∧ ¬ Results 0x7fc00000 0 := by
  decide

theorem finite_mismatch_rejected : ¬ Results 0x40000000 0x3f800000 := by decide

theorem denominator_handoff :
    ∃ output, Results 0x3f800000 output ∧
      finiteReal output = some (TorchLean.Floats.round32 (1/(1:ℝ))) :=
  result_exists_of_sum_error _ 1 1 (1/2) Bounds.positive_one_real
    (by norm_num) (by norm_num) (by norm_num)

end Ptx.Binary32.Reciprocal.Checks
