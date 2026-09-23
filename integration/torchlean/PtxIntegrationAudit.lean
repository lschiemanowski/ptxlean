import PtxTorchLean
import PtxTensorBridge
import PtxBinary32
import PtxBinary32Examples
import PtxBinary32Bounds
import PtxBinary32Error

/-! Explicit public integration endpoints and binary32 reference dependencies.
Fresh elaboration is checked by check.py; imported build logs are not reused. -/

#print axioms PtxTorchLean.affineSquare
#print axioms PtxTorchLean.forward_polynomial
#print axioms PtxTorchLean.checked_vjp
#print axioms PtxTorchLean.exact_tape_success_vjp
#print axioms PtxTorchLean.checked_success
#print axioms PtxTorchLean.checked_success_vjp
#print axioms PtxTorchLean.unsigned_min_scalar_embedding

#print axioms PtxTorchLean.TensorBridge.view_apply
#print axioms PtxTorchLean.TensorBridge.view_map
#print axioms PtxTorchLean.TensorBridge.layout_bounds
#print axioms PtxTorchLean.TensorBridge.realView_eq_map
#print axioms PtxTorchLean.TensorBridge.completed_unsigned
#print axioms PtxTorchLean.TensorBridge.completed_unsigned_tensor
#print axioms PtxTorchLean.TensorBridge.completed_real_add
#print axioms PtxTorchLean.TensorBridge.completed_bounds
#print axioms PtxTorchLean.TensorBridge.candidate_unsigned_tensor
#print axioms PtxTorchLean.TensorBridge.candidate_execution_agree
#print axioms PtxTorchLean.TensorBridge.execution_exists
#print axioms PtxTorchLean.TensorBridge.real_execution_exists
#print axioms PtxTorchLean.TensorBridge.view_bounded_apply
#print axioms PtxTorchLean.TensorBridge.wraparound_execution
#print axioms PtxTorchLean.TensorBridge.wraparound_not_fitting

#print axioms Ptx.Binary32.encode_decode
#print axioms Ptx.Binary32.decode_encode
#print axioms Ptx.Binary32.finiteReal_none
#print axioms Ptx.Binary32.finiteReal_some
#print axioms Ptx.Binary32.finiteReal_isSome
#print axioms Ptx.Binary32.finite_not_nan
#print axioms Ptx.Binary32.envelope_self
#print axioms Ptx.Binary32.envelope_exists
#print axioms Ptx.Binary32.envelope_nan
#print axioms Ptx.Binary32.envelope_non_nan
#print axioms Ptx.Binary32.envelope_finite_eq
#print axioms Ptx.Binary32.envelope_finite
#print axioms Ptx.Binary32.results_exists
#print axioms Ptx.Binary32.reference_round
#print axioms Ptx.Binary32.results_round
#print axioms Ptx.Binary32.results_abs_error
#print axioms Ptx.Binary32.decode
#print axioms Ptx.Binary32.encode
#print axioms Ptx.Binary32.isNaN
#print axioms Ptx.Binary32.isFinite
#print axioms Ptx.Binary32.finiteReal
#print axioms Ptx.Binary32.Envelope
#print axioms Ptx.Binary32.reference
#print axioms Ptx.Binary32.Results
#print axioms Ptx.Binary32.exact

#print axioms Ptx.Binary32.Examples.signed_zero_bits_distinct
#print axioms Ptx.Binary32.Examples.zero_signs_finite
#print axioms Ptx.Binary32.Examples.smallest_subnormal
#print axioms Ptx.Binary32.Examples.normal_boundary
#print axioms Ptx.Binary32.Examples.ordinary_add
#print axioms Ptx.Binary32.Examples.tie_even_down
#print axioms Ptx.Binary32.Examples.tie_odd_up
#print axioms Ptx.Binary32.Examples.subnormal_add_preserved
#print axioms Ptx.Binary32.Examples.negative_zero_product
#print axioms Ptx.Binary32.Examples.zero_sign_add
#print axioms Ptx.Binary32.Examples.finite_inputs_overflow
#print axioms Ptx.Binary32.Examples.infinity_opposite_invalid
#print axioms Ptx.Binary32.Examples.infinity_times_zero_invalid
#print axioms Ptx.Binary32.Examples.nan_payload_freedom
#print axioms Ptx.Binary32.Examples.signaling_nan_envelope
#print axioms Ptx.Binary32.Examples.exceptional_not_real

#print axioms Ptx.Binary32.Bounds.maxFinite_eq
#print axioms Ptx.Binary32.Bounds.finiteReal_spec
#print axioms Ptx.Binary32.Bounds.reference_finite
#print axioms Ptx.Binary32.Bounds.round_of_range
#print axioms Ptx.Binary32.Bounds.results_error
#print axioms Ptx.Binary32.Bounds.finite_result_exists
#print axioms Ptx.Binary32.Bounds.add_range_of_magnitudes
#print axioms Ptx.Binary32.Bounds.mul_range_of_magnitudes
#print axioms Ptx.Binary32.Bounds.unit_range
#print axioms Ptx.Binary32.Bounds.positive_one_real
#print axioms Ptx.Binary32.Bounds.negative_one_real
#print axioms Ptx.Binary32.Bounds.one_negative_one_results

#print axioms Ptx.Binary32.Error.budget_nonnegative
#print axioms Ptx.Binary32.Error.add_propagation
#print axioms Ptx.Binary32.Error.mul_propagation
#print axioms Ptx.Binary32.Error.add_results
#print axioms Ptx.Binary32.Error.mul_results
#print axioms Ptx.Binary32.Error.add_exists
#print axioms Ptx.Binary32.Error.mul_exists
#print axioms Ptx.Binary32.Error.rounded_add_range
#print axioms Ptx.Binary32.Error.affine_results
#print axioms Ptx.Binary32.Error.affine_exists
