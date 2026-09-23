import PtxBinary32

/-! Kernel-checked encoded boundary examples. These test the selected software
reference and the conservative envelope; they are not hardware measurements. -/
namespace Ptx.Binary32.Examples

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

theorem signed_zero_bits_distinct : (0 : Word) ≠ (0x80000000 : Word) := by decide

theorem zero_signs_finite : isFinite 0 = true ∧ isFinite 0x80000000 = true := by decide

theorem smallest_subnormal :
    FloatLib.Floats.ExecFloat.Binary.isSubnormal (decode 1) = true := by decide

theorem normal_boundary :
    FloatLib.Floats.ExecFloat.Binary.isSubnormal (decode 0x007fffff) = true ∧
    FloatLib.Floats.ExecFloat.Binary.isSubnormal (decode 0x00800000) = false ∧
    isFinite 0x00800000 = true := by decide

theorem ordinary_add : reference .add 0x3f800000 0x3f800000 = 0x40000000 := by decide

theorem tie_even_down : reference .add 0x3f800000 0x33800000 = 0x3f800000 := by decide

theorem tie_odd_up : reference .add 0x3f800001 0x33800000 = 0x3f800002 := by decide

theorem subnormal_add_preserved : reference .add 1 1 = 2 := by decide

theorem negative_zero_product : reference .mul 0x80000000 0x3f800000 = 0x80000000 := by decide

theorem zero_sign_add : reference .add 0 0x80000000 = 0 ∧
    reference .add 0x80000000 0x80000000 = 0x80000000 := by decide

theorem finite_inputs_overflow : isFinite 0x7f7fffff = true ∧
    reference .add 0x7f7fffff 0x7f7fffff = 0x7f800000 ∧
    isFinite (reference .add 0x7f7fffff 0x7f7fffff) = false := by decide

theorem infinity_opposite_invalid : isNaN (reference .add 0x7f800000 0xff800000) = true := by decide

theorem infinity_times_zero_invalid : isNaN (reference .mul 0x7f800000 0) = true := by decide

/-- Distinct quiet NaN payloads both belong; reference payload is not imposed. -/
theorem nan_payload_freedom : Results .add 0x7f800000 0xff800000 0x7fc00000 ∧
    Results .add 0x7f800000 0xff800000 0xffc00001 := by unfold Results; decide

/-- Inclusion in the envelope is deliberately not a signaling-NaN realizability claim. -/
theorem signaling_nan_envelope : Results .add 0x7f800000 0xff800000 0x7f800001 := by unfold Results; decide

theorem exceptional_not_real : finiteReal 0x7f800000 = none ∧
    finiteReal 0x7fc00000 = none :=
  ⟨finiteReal_none _ (by decide), finiteReal_none _ (by decide)⟩

end Ptx.Binary32.Examples
