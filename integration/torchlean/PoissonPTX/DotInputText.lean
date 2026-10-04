import PoissonPTX.DotInputComplete
import PoissonPTX.Text

namespace PtxTorchLean.Poisson.PTX.DotInput

/-- The scratch symbol stands for the allocated shared address parameter;
the lane copy is justified by lane_copy, not by unrestricted 64/32-bit equality. -/
def render : Flow.Instr → String
  | .data (.data (.mov 3 (.imm _))) => "mov.u64 %shared, scratch;"
  | .data (.data (.mov 12 (.reg 14))) => "mov.u32 %global, %lane;"
  | .data (.data (.mov 8 (.imm w))) =>
      if w=0 then "mov.f64 %acc, 0d0000000000000000;" else Text.data (.mov 8 (.imm w))
  | .data (.data op) => Text.data op
  | .context dst .arena => s!"ld.param.u64 {Text.register dst}, [arena];"
  | .context dst .lane => s!"mov.u32 {Text.register dst}, %tid.x;"
  | .context dst .group => s!"mov.u32 {Text.register dst}, %ctaid.x;"
  | .compare 0 .ge a b => s!"setp.ge.u32 %p0, {Text.operand a}, {Text.operand b};"
  | .branch 0 true target => s!"@%p0 bra #{target};"
  | .jump target => s!"bra #{target};"
  | _ => "unsupported dot input instruction"

def rendered (count : Nat) (left right : Word) : List String :=
  (inputProgram count left right 0).map render

end PtxTorchLean.Poisson.PTX.DotInput
