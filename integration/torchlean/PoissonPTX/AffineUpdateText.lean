import PoissonPTX.AffineUpdateEntry
import PoissonPTX.AssemblyText

namespace PtxTorchLean.Poisson.PTX.AffineUpdate

/-- Render the actual proved update_p entry, including its in-place output. -/
def rendered (count : BitVec 32) (coefficient input shift : Word) : List String :=
  (entry count coefficient input shift input).map (Assembly.Text.instruction 0)

theorem entry_length : (entry count coefficient input shift output).length=25 := by
  simp [entry,VectorEntry.program,Assembly.prologue,code,ScalarLoad.code,loadCode,storeCode,PTX.addressCode]

end PtxTorchLean.Poisson.PTX.AffineUpdate
