import PoissonPTX.CellFinalKernel
import PoissonPTX.ContractionText

namespace PtxTorchLean.Poisson.PTX.CellFinal

/-- Render the same final-body list used by the fetched correctness and
existence proofs; the outer activity guard is checked separately. -/
def rendered (width : Nat) (b d output : Word) : List String :=
  (program width b d output).map fun instruction =>
    match instruction with
    | .data op => Contraction.render op
    | i => Text.instruction i

end PtxTorchLean.Poisson.PTX.CellFinal
