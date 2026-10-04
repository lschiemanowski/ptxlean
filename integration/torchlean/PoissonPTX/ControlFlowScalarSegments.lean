import PoissonPTX.ControlFlowSegments
import PoissonPTX.IndexedScalar

namespace PtxTorchLean.Poisson.PTX.Flow

theorem scalar_segment (run : Sequence ctx (code.map (Instr.data ∘ Indexed.Instr.data)) s t) :
    PTX.Block code s.core t.core ∧ t={s with core:=t.core} := by
  obtain ⟨block,pred,halt⟩ := sequence_data_block (ctx:=ctx) (s:=s) (t:=t) (code:=code.map Indexed.Instr.data)
    (by simpa only [List.map_map] using run)
  refine ⟨Indexed.underlying_block block,?_⟩
  cases t
  simp_all only

theorem scalar_sequence (block : PTX.Block code s.core t) (running : s.halted=false) :
    Sequence ctx (code.map (Instr.data ∘ Indexed.Instr.data)) s {s with core:=t} := by
  simpa only [List.map_map] using sequence_data (Indexed.scalar_block block) running

end PtxTorchLean.Poisson.PTX.Flow
