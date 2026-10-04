import PoissonPTX.ScalarSourceBridge
import PoissonPTX.ScalarAlphaCorrect

namespace PtxTorchLean.Poisson.PTX.Scalar.Alpha

def chunks : List Chunk := [
  .load64 .denominator 4,.load64 .rho 5,.load32 .active 21,.load32 .broken 22,
  .pure Coefficient.alphaCode,.store32 .broken (.reg 22),.store32 .useStep (.reg 21),
  .pure (ConditionalDivide.code 5 4),.store64 .alpha (.reg 6)]

theorem chunks_code : chunksCode offset chunks=body offset := by
  simp [chunksCode,chunks,Chunk.code,body,prefixCode,flagCode,Coefficient.inputCode,List.append_assoc]

theorem chunks_valid : ∀ chunk∈chunks, chunk.valid := by
  simp [chunks,Chunk.valid,Field.width,Coefficient.alphaCode,Coefficient.finiteCode,ConditionalDivide.code,
    Observed.noMemory,Observed.keepsBase,Observed.indexedKeepsBase,Observed.dataKeepsBase,segment,Flow.segment]

theorem reads_before_writes : ReadBeforeWrite (footprints offset pc chunks) := by
  simp [ReadBeforeWrite,footprints,chunks,Chunk.footprint,Chunk.code,Coefficient.alphaCode,Coefficient.finiteCode,
    ConditionalDivide.code,load64Code,load32Code,store32Code,address4Code,ops,ScalarLoad.code]

theorem admitted_body {a : Arena} (actual : Observed.Sequence ctx (body a.offset) s events t)
    (running : s.halted=false) (ready : a.Ready s)
    (compatible : Sources.Compatible s.core.memory events source) (admitted : Sources.NoFuture events source) :
    ∃ value, Allowed a s.core.global value ∧ t=finished a (beforeDivide ctx a s) value := by
  rw [← chunks_code] at actual
  have replay := chunks_replay actual chunks_valid running ready reads_before_writes compatible admitted
  rw [chunks_code] at replay
  exact body_result replay running ready

end PtxTorchLean.Poisson.PTX.Scalar.Alpha
