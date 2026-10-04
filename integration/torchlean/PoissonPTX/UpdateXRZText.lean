import PoissonPTX.UpdateXRZExists
import PoissonPTX.AssemblyText

namespace PtxTorchLean.Poisson.PTX.UpdateXRZ

/-- The boundary selector moves the exact binary64 encoding of one. Remaining
instructions use the shared renderer and preserve their emitted registers. -/
def instruction : Flow.Instr → String
  | .select 0 true 5 (.imm word) =>
      if word=PreconditionUpdate.one then "@%p0 mov.f64 %b, 0d3ff0000000000000;"
      else Assembly.Text.instruction 0 (.select 0 true 5 (.imm word))
  | op => Assembly.Text.instruction 0 op

def rendered (count : BitVec 32) (alpha p x ap r diagonal boundary z : Word) : List String :=
  (entry count alpha p x ap r diagonal boundary z).map instruction

end PtxTorchLean.Poisson.PTX.UpdateXRZ
