import PoissonPTX.AssemblyEntry
import PoissonPTX.RoundedLaunch

namespace PtxTorchLean.Poisson.PTX.Assembly

/-- Expose the original assembly entry as the common guard, unchanged loop and
store body, and final return. Branch destinations remain the original PCs. -/
def guardedBody (count : BitVec 32) (offsets entries element : Word) (mask : Bool) (boundary output : Word) : List Flow.Instr :=
  (prepareCode offsets).map Flow.Instr.data ++
    Flow.Window.header (entryPrefix count offsets).length 19 20 (body entries element) ++
    (body entries element).map Flow.Instr.data ++ [.jump (entryPrefix count offsets).length] ++
    (if mask then maskCode boundary else []) ++
    ((storeCode 8 12 output).map Indexed.Instr.data).map Flow.Instr.data

theorem entry_guarded : entryCode count offsets entries element mask boundary output=
    VectorFlowEntry.program count (guardedBody count offsets entries element mask boundary output) := by
  simp only [entryCode,Flow.Window.program,entryPrefix,tailCode,outputCode,VectorFlowEntry.program,guardedBody,List.append_assoc]

end PtxTorchLean.Poisson.PTX.Assembly
