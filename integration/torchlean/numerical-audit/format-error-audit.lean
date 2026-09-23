import NN.Floats.IEEEExec.Bridge.Finite
import NN.Floats.FP32.Error
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
#print axioms ExecFloat.Binary.toBits32_ofBits32
#print axioms ExecFloat.Binary.ofBits32_toBits32
#print axioms Model.Proof.add_eq_spec
#print axioms Model.Proof.mul_eq_spec
#print axioms Model.Proof.fma_eq_spec
#print axioms ExecFloat.Binary.toModel_add
#print axioms TorchLean.Floats.IEEE754.IEEE32Exec.toReal_add_eq_fp32Round_of_isFinite
#print axioms TorchLean.Floats.IEEE754.IEEE32Exec.toReal_mul_eq_fp32Round_of_isFinite
#print axioms TorchLean.Floats.FP32.round_abs_error
#print axioms TorchLean.Floats.FP32.round_relative_error_of_normal
example (x y : ExecFloat.Binary 8 23) : ExecFloat.add x y = ExecFloat.Spec.add x y := ExecFloat.Proof.add_eq_spec x y

run_cmd do
  for name in (← Lean.getEnv).header.moduleNames do
    Lean.logInfo m!"AUDIT_IMPORT {name}"
