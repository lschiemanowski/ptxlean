import PoissonPTX.ReductionNativeCode
import PoissonPTX.Text

namespace PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native

/-- Branch labels are resolved by the frontend to relative instruction indices.
All other text is rendered directly from the proved native instruction list. -/
def render : Instr → String
  | .data (.store64 sp (.offset r 0) src) => Text.data (.store64 sp (.reg r) src)
  | .data op => Text.data op
  | .compare count => s!"setp.ge.u32 %p0, %lane, {count};"
  | .branch target => s!"@%p0 bra #{target};"
  | .sync resource => s!"bar.sync {resource.val};"

def rendered : List String := code.map render

/-- The emitted initial store omits the address's zero displacement. This
normalization is exact modular address equality, not an ignored instruction. -/
theorem zero_displacement (s : PTX.State) (r : Nat) :
    Operand.eval s (.offset r 0)=Operand.eval s (.reg r) := by simp [Operand.eval]

end PtxTorchLean.Poisson.PTX.Concurrent.Reduction.Native
