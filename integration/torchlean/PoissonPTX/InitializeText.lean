import PoissonPTX.InitializeEntry
import PoissonPTX.UpdateXRZText

namespace PtxTorchLean.Poisson.PTX.Initialize

/-- Spell the two literal zero-word instructions in emitted f64 notation. -/
def instruction : Flow.Instr → String
  | .select 0 true 4 (.imm 0) => "@%p0 mov.f64 %a, 0d0000000000000000;"
  | .data (.data (.store64 .global (.reg 2) (.imm 0))) => "st.global.f64 [%addr], 0d0000000000000000;"
  | op => UpdateXRZ.instruction op

def rendered (count : BitVec 32) (boundary input rhs r diagonal z p x : Word) : List String :=
  (entry count boundary input rhs r diagonal z p x).map instruction

end PtxTorchLean.Poisson.PTX.Initialize
