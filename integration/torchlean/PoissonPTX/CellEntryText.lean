import PoissonPTX.CellEntry
import PoissonPTX.CellGatherText

namespace PtxTorchLean.Poisson.PTX.CellEntry

def label (pc : Nat) : String := if pc=20 then "stage_0_done" else s!"entry_{pc}"

def render : Instr → String
  | .setup op => CellPrologue.render op
  | .gather op => CellGather.render op
  | .skip target => s!"@!%live bra {label target};"
  | .sync => "bar.sync 0;"

/-- Render the same fetched program, inserting the branch label immediately
before instruction 20. Labels do not themselves advance the program counter. -/
def rendered (width : Nat) (cells source : Word) : List String :=
  (program width cells source).zipIdx |>.flatMap fun (i,pc) =>
    (if pc=20 then [label pc++":"] else [])++[render i]

end PtxTorchLean.Poisson.PTX.CellEntry
