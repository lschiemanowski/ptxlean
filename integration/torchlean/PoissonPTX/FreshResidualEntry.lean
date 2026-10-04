import PoissonPTX.KernelToFlowRun
import PoissonPTX.VectorFlowEntry
import PoissonPTX.ParallelResidualLayout

namespace PtxTorchLean.Poisson.PTX.FreshResidual

def entry (count : BitVec 32) (rhs ap output : Word) : List Flow.Instr :=
  (Kernel.Residual.program count rhs ap output).map Kernel.ToFlow.instruction

theorem entry_guarded : entry count rhs ap output =
    VectorFlowEntry.program count ((Residual.code rhs ap output).map (Flow.Instr.data ∘ Indexed.Instr.data)) := by
  simp [entry,Kernel.Residual.program,Kernel.Residual.prologue,Kernel.ToFlow.instruction,
    VectorFlowEntry.program,Assembly.prologue,List.map_map,Function.comp_def]

theorem entry_length : (entry count rhs ap output).length=20 := by
  simp [entry,Kernel.Residual.program,Kernel.Residual.prologue,Residual.code,loadCode,storeCode,addressCode]

/-- The numerical result is inherited from the original fetched residual
kernel through the proved instruction translation. -/
theorem entry_correct (run : Flow.Runs ctx (entry count rhs ap output) s t)
    (pc : s.core.pc=0) (running : s.halted=false) (done : t.halted=true)
    (live : Kernel.Residual.live ctx count)
    (hr : Valid64 s.core.globalStart s.core.globalBytes (address64 ctx.arena (Kernel.Residual.index ctx) rhs).toNat)
    (ha : Valid64 s.core.globalStart s.core.globalBytes (address64 ctx.arena (Kernel.Residual.index ctx) ap).toNat)
    (ho : Valid64 s.core.globalStart s.core.globalBytes (address64 ctx.arena (Kernel.Residual.index ctx) output).toNat) :
    decode (read64 t.core.global (address64 ctx.arena (Kernel.Residual.index ctx) output).toNat)=
      decode (read64 s.core.global (address64 ctx.arena (Kernel.Residual.index ctx) rhs).toNat)-
      decode (read64 s.core.global (address64 ctx.arena (Kernel.Residual.index ctx) ap).toNat) := by
  have result := Kernel.Residual.fetched_correct ctx (Kernel.ToFlow.project s) (Kernel.ToFlow.project t)
    count rhs ap output pc running live
    (by simpa only [Kernel.Residual.setup_address,Kernel.ToFlow.project] using hr)
    (by simpa only [Kernel.Residual.setup_address,Kernel.ToFlow.project] using ha)
    (by simpa only [Kernel.Residual.setup_address,Kernel.ToFlow.project] using ho)
    (Kernel.ToFlow.run_project run running done)
  simpa only [Kernel.Residual.setup_address,Kernel.ToFlow.project] using result.1

end PtxTorchLean.Poisson.PTX.FreshResidual
