import PoissonPTX.AssemblyEntry
import PoissonPTX.AssemblyText

namespace PtxTorchLean.Poisson.PTX.Assembly.Text

/-- The emitted dialect writes zero as an f64 bit-pattern literal. Both mov
forms copy precisely the same 64 bits in the scalar semantics. -/
def fullInstruction (origin finish : Nat) : Flow.Instr → String
  | .data (.data (.mov 8 (.imm w))) => if w=0 then "mov.f64 %acc, 0d0000000000000000;" else instruction finish (.data (.data (.mov 8 (.imm w))))
  | .select 0 true 8 (.imm w) => if w=0 then "@%p0 mov.f64 %acc, 0d0000000000000000;" else instruction finish (.select 0 true 8 (.imm w))
  | .jump target => if target=origin then "bra loop;" else instruction finish (.jump target)
  | op => instruction finish op

/-- Labels are inserted at positions computed from the same instruction lists
used by the whole-entry execution theorems. -/
def fullRendered (count : BitVec 32) (offsets entries element : Word) (mask : Bool) (boundary output : Word) : List String :=
  let origin := (entryPrefix count offsets).length
  let finish := (beforeOutput count offsets entries element).length
  (entryCode count offsets entries element mask boundary output).zipIdx.flatMap fun (op,pc) =>
    (if pc=origin then ["loop:"] else if pc=finish then ["done:"] else [])++[fullInstruction origin finish op]

def fullShape (count : BitVec 32) (offsets entries element : Word) (mask : Bool) (boundary output : Word) :
    Nat × List (Nat × Nat) :=
  let code := entryCode count offsets entries element mask boundary output
  (code.length,code.zipIdx.filterMap fun (op,pc) => match op with
    | .branch _ _ target | .jump target => some (pc,target) | _ => none)

end PtxTorchLean.Poisson.PTX.Assembly.Text
