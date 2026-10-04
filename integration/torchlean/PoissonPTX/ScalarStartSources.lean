import PoissonPTX.ScalarSourceBridge
import PoissonPTX.ScalarStartPublication
import PoissonPTX.ScalarStartExists

namespace PtxTorchLean.Poisson.PTX.Scalar.Start

def chunks : List Chunk := [
  .load64 .rhsSquare 4,.pure [.sqrt 4 (.reg 4)],.store64 .rhsNorm (.reg 4),.store64 .residual (.reg 4),
  .load64 .rtol 5,.load64 .atol 6,
  .pure [.base (.data (.data (.fp .mul 5 (.reg 5) (.reg 4)))),.max 5 (.reg 5) (.reg 6)],
  .store64 .tolerance (.reg 5),.store32 .active (.imm 1),.store32 .broken (.imm 0)]

theorem chunks_code : chunksCode offset chunks=body offset := by
  simp [chunksCode,chunks,Chunk.code,body,middleCode,tailCode,List.append_assoc]

theorem chunks_valid : ∀ chunk∈chunks, chunk.valid := by
  simp [chunks,Chunk.valid,Field.width,Observed.noMemory,Observed.keepsBase,Observed.indexedKeepsBase,
    Observed.dataKeepsBase,segment,Flow.segment]

theorem reads_before_writes : ReadBeforeWrite (footprints offset pc chunks) := by
  simp [ReadBeforeWrite,footprints,chunks,Chunk.footprint,Chunk.code,load64Code,store64Code,store64Ops,
    store32Code,address4Code,ops,ScalarLoad.code]

/-- Candidate bits are justified from initial memory using actual field
accesses and necessary same-thread source rules, before arithmetic replay. -/
theorem admitted_body {a : Arena} (actual : Observed.Sequence ctx (body a.offset) s events t)
    (running : s.halted=false) (ready : a.Ready s)
    (compatible : Sources.Compatible s.core.memory events source) (admitted : Sources.NoFuture events source) : Result a s t := by
  rw [← chunks_code] at actual
  have replay := chunks_replay actual chunks_valid running ready reads_before_writes compatible admitted
  rw [chunks_code] at replay
  exact body_result replay running ready

end PtxTorchLean.Poisson.PTX.Scalar.Start
