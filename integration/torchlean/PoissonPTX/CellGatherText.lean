import PoissonPTX.CellGatherLayout
import PoissonPTX.Text

namespace PtxTorchLean.Poisson.PTX.CellGather

/-- Exact generated gather forms; existing 64-bit operations use their shared
renderer. Register 18 is the unsigned node loaded from connectivity. -/
def render : Indexed.Instr → String
  | .data op => Text.data op
  | .mad32 dst a scale b => s!"mad.lo.u32 {Text.register dst}, {Text.register a}, {scale.toNat}, {Text.register b};"
  | .wide4 dst src => s!"mul.wide.u32 {Text.register dst}, {Text.register src}, 4;"
  | .load32 dst addr => s!"ld.global.u32 {Text.register dst}, [{Text.register addr}];"

def rendered (width : Nat) (cells source : Word) : List String := (code width cells source).map render

end PtxTorchLean.Poisson.PTX.CellGather
