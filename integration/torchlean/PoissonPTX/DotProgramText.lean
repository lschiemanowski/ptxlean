import PoissonPTX.DotCompletedInput

namespace PtxTorchLean.Poisson.PTX.Concurrent.Dot

/-- Render the same complete list used by the concurrent theorems. Targets are
absolute instruction positions; scratch denotes its launch allocation. -/
def render : NativeFlow.Instr → String
  | .sync resource => s!"bar.sync {resource.val};"
  | .flow (.data (.data (.store64 sp (.offset r 0) src))) => Text.data (.store64 sp (.reg r) src)
  | .flow (.compare 0 .ne a b) => s!"setp.ne.u32 %p0, {Text.operand a}, {Text.operand b};"
  | .flow (.predRet 0 true) => "@%p0 ret;"
  | .flow .ret => "ret;"
  | .flow i => DotInput.render i

def rendered (count : Nat) (left right output : Word) : List String :=
  (program count left right output 0).map render

end PtxTorchLean.Poisson.PTX.Concurrent.Dot
