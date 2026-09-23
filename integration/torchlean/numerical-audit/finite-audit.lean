import NN.Floats.IEEEExec.Bridge.Finite

-- This file checks existing APIs only; it defines no PTX numerical semantics.
open FloatLib.Floats
open FloatLib.Floats.ExecFloat.Binary

-- Instantiate the generic lossless interchange proof at the actual 32-bit type.
example (bits : BitVec 32) :
    toNatBits (ofNatBits bits.toNat : ExecFloat.Binary 8 23) = bits.toNat := by
  exact toNatBits_ofNatBits_of_lt bits.toNat bits.isLt

example (value : ExecFloat.Binary 8 23) :
    (ofNatBits (toNatBits value) : ExecFloat.Binary 8 23) = value :=
  ofNatBits_toNatBits value

#print axioms TorchLean.Floats.IEEE754.IEEE32Exec.toModel_add
#print axioms TorchLean.Floats.IEEE754.IEEE32Exec.toModel_mul
#print axioms TorchLean.Floats.IEEE754.IEEE32Exec.model_isFinite_quietNaN
#print axioms TorchLean.Floats.IEEE754.IEEE32Exec.model_isFinite_chooseNaN2
#print axioms TorchLean.Floats.IEEE754.IEEE32Exec.roundAt_binary32
#print axioms TorchLean.Floats.IEEE754.IEEE32Exec.toReal_add_eq_fp32Round_of_isFinite
#print axioms TorchLean.Floats.IEEE754.IEEE32Exec.toReal_mul_eq_fp32Round_of_isFinite
#print axioms TorchLean.Floats.IEEE754.IEEE32Exec.fp32Round_eq_computed
#print axioms TorchLean.Floats.IEEE754.IEEE32Exec.toReal_mul_eq_computed_of_isFinite
#print axioms FloatLib.Floats.ExecFloat.Binary.toModel_ofModel
#print axioms FloatLib.Floats.ExecFloat.Binary.ofModel_toModel
#print axioms FloatLib.Floats.ExecFloat.Binary.ofNatBits_toNatBits
#print axioms FloatLib.Floats.ExecFloat.Binary.toNatBits_ofNatBits_of_lt
#print axioms FloatLib.Floats.ExecFloat.Binary.toModel_add
#print axioms FloatLib.Floats.ExecFloat.Binary.toModel_mul
#print axioms FloatLib.Floats.ExecFloat.Proof.add_eq_spec
#print axioms FloatLib.Floats.ExecFloat.Proof.mul_eq_spec
#print axioms FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt
#print axioms FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_mul_eq_roundAt

run_cmd do
  for name in (← Lean.getEnv).header.moduleNames do
    Lean.logInfo m!"AUDIT_IMPORT {name}"
