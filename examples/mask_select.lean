import Ptx.MaskSelect

-- Decimal results: 52 (0x34), then 99 (the fallback).
#eval (Ptx.Scalar.MaskSelect.answer 0x1234 99 0xff).toNat
#eval (Ptx.Scalar.MaskSelect.answer 0x100 99 0xff).toNat

-- The generic proofs, not just these two calculations, establish kernel behavior.
#check Ptx.Scalar.MaskSelect.execution_exists
#check Ptx.Scalar.MaskSelect.correct
#check Ptx.Scalar.MaskSelect.memory_safe
#check Ptx.Scalar.MaskSelect.other_memory
