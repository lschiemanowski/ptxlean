import PoissonPTX.Machine
import FloatLib.Floats.Formats.IEEE754.Native.AddSub

namespace PtxTorchLean.Poisson.PTX
open FloatLib.Floats.ExecFloat

/-- For finite decoded inputs the primitive subtraction contract agrees with
FloatLib's software binary64 operation (nearest-even, including overflow).
The finite premises concern inputs; no output or phase result is assumed. -/
theorem sub_software (h : FP.Result .sub a b out)
    (ha : (decode a).isFinite = true) (hb : (decode b).isFinite = true) :
    Binary.ofFloat (decode out) = Binary.ofFloat (decode a) - Binary.ofFloat (decode b) := by
  rw [show decode out = decode a - decode b from h]
  exact Binary.ofFloat_sub_of_isFinite _ _ ha hb

end PtxTorchLean.Poisson.PTX
