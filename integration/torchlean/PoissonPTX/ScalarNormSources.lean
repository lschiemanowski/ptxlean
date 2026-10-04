import PoissonPTX.ScalarEntrySources
import PoissonPTX.ScalarNorm
import PoissonPTX.ScalarRestartFlag

namespace PtxTorchLean.Poisson.PTX.Scalar.Norm

def chunks : List Chunk := [.load64 .trueSquare 4,.pure [.sqrt 4 (.reg 4)],.store64 .residual (.reg 4)]

theorem chunks_code : chunksCode offset chunks=body (offset .trueSquare) (offset .residual) := by
  simp [chunksCode,chunks,Chunk.code,body,List.append_assoc]

theorem chunks_valid : ∀ chunk∈chunks, chunk.valid := by
  simp [chunks,Chunk.valid,Field.width,Observed.noMemory,Observed.keepsBase,segment]

theorem reads_before_writes : ReadBeforeWrite (footprints offset pc chunks) := by
  simp [ReadBeforeWrite,footprints,chunks,Chunk.footprint,Chunk.code,load64Code,ScalarLoad.code,ops]

theorem admitted_replay {a : Arena}
    (actual : Observed.Runs a.context (entry (a.offset .trueSquare) (a.offset .residual)) (a.start memory regs) events final)
    (done : final.halted=true) (compatible : Sources.Compatible (a.start memory regs).core.memory events source)
    (admitted : Sources.NoFuture events source) :
    Scalar.Runs a.context (entry (a.offset .trueSquare) (a.offset .residual)) (a.start memory regs) final := by
  have run : Observed.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) events final := by
    simpa only [chunks_code,entry] using actual
  simpa only [chunks_code,entry] using chunks_entry_replay run done chunks_valid (fun _ => reads_before_writes) compatible admitted

end PtxTorchLean.Poisson.PTX.Scalar.Norm

namespace PtxTorchLean.Poisson.PTX.Scalar.RestartFlag

def chunks : List Chunk := [.store32 .active (.imm 1)]

theorem chunks_code : chunksCode offset chunks=body (offset .active) := by
  simp [chunksCode,chunks,Chunk.code,body]

theorem chunks_valid : ∀ chunk∈chunks, chunk.valid := by simp [chunks,Chunk.valid,Field.width]

theorem reads_before_writes : ReadBeforeWrite (footprints offset pc chunks) := by
  simp [ReadBeforeWrite,footprints,chunks,Chunk.footprint]

theorem admitted_replay {a : Arena}
    (actual : Observed.Runs a.context (entry (a.offset .active)) (a.start memory regs) events final)
    (done : final.halted=true) (compatible : Sources.Compatible (a.start memory regs).core.memory events source)
    (admitted : Sources.NoFuture events source) :
    Scalar.Runs a.context (entry (a.offset .active)) (a.start memory regs) final := by
  have run : Observed.Runs a.context (program (chunksCode a.offset chunks)) (a.start memory regs) events final := by
    simpa only [chunks_code,entry] using actual
  simpa only [chunks_code,entry] using chunks_entry_replay run done chunks_valid (fun _ => reads_before_writes) compatible admitted

end PtxTorchLean.Poisson.PTX.Scalar.RestartFlag
