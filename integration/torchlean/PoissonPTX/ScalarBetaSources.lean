import PoissonPTX.ScalarSourceBridge
import PoissonPTX.ScalarBetaExists

namespace PtxTorchLean.Poisson.PTX.Scalar.Beta

def chunks : List Chunk := [
  .load64 .rhoNext 4,.load64 .rho 5,.load32 .active 21,.load32 .broken 22,
  .pure Coefficient.betaBrokenCode,.store32 .broken (.reg 22),.load32 .useStep 21,
  .pure selectCode,.pure (ConditionalDivide.code 4 5),.store64 .beta (.reg 6),.store64 .rho (.reg 4),
  .load64 .rr 4,.load64 .tolerance 5,.pure [.base (.data (.data (.fp .mul 5 (.reg 5) (.reg 5))))],
  .pure Coefficient.betaFinalCode,.store32 .active (.reg 21)]

theorem chunks_code : chunksCode offset chunks=body offset := by
  simp [chunksCode,chunks,Chunk.code,body,prefixCode,middleCode,tailCode,Coefficient.inputCode,List.append_assoc]

theorem chunks_valid : ∀ chunk∈chunks, chunk.valid := by
  simp [chunks,Chunk.valid,Field.width,Coefficient.betaBrokenCode,Coefficient.betaFinalCode,Coefficient.finiteCode,
    ConditionalDivide.code,selectCode,Observed.noMemory,Observed.keepsBase,Observed.indexedKeepsBase,Observed.dataKeepsBase,
    segment,Flow.segment]

theorem reads_before_writes : ReadBeforeWrite (footprints offset pc chunks) := by
  simp [ReadBeforeWrite,footprints,chunks,Chunk.footprint,Chunk.code,Coefficient.betaBrokenCode,Coefficient.betaFinalCode,
    Coefficient.finiteCode,ConditionalDivide.code,selectCode,load64Code,load32Code,store64Code,store64Ops,
    store32Code,address4Code,ops,ScalarLoad.code,Nat.add_assoc]

theorem admitted_body {a : Arena} (actual : Observed.Sequence ctx (body a.offset) s events t)
    (running : s.halted=false) (ready : a.Ready s)
    (compatible : Sources.Compatible s.core.memory events source) (admitted : Sources.NoFuture events source) : Result ctx a s t := by
  rw [← chunks_code] at actual
  have replay := chunks_replay actual chunks_valid running ready reads_before_writes compatible admitted
  rw [chunks_code] at replay
  exact body_result replay running ready

end PtxTorchLean.Poisson.PTX.Scalar.Beta
